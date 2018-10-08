#include <mysql2_ext.h>

#include "mysql_enc_to_ruby.h"

static rb_encoding *binaryEncoding;

/* on 64bit platforms we can handle dates way outside 2038-01-19T03:14:07
 *
 * (9999*31557600) + (12*2592000) + (31*86400) + (11*3600) + (59*60) + 59
 */
#define MYSQL2_MAX_TIME 315578267999ULL

/* 0000-1-1 00:00:00 UTC
 *
 * (0*31557600) + (1*2592000) + (1*86400) + (0*3600) + (0*60) + 0
 */
#define MYSQL2_MIN_TIME 2678400ULL

#define GET_RESULT(self) \
  mysql2_result_wrapper *wrapper; \
  Data_Get_Struct(self, mysql2_result_wrapper, wrapper);

typedef struct {
  int symbolizeKeys;
  int resultAs;
  int castBool;
  int cacheRows;
  int cast;
  int streaming;
  ID db_timezone;
  ID app_timezone;
  VALUE block_given;
} result_each_args;

extern VALUE mMysql2, cMysql2Client, cMysql2Error;
static VALUE cMysql2Result, cDateTime, cDate;
static VALUE opt_decimal_zero, opt_float_zero, opt_time_year, opt_time_month, opt_utc_offset;
static ID intern_new, intern_utc, intern_local, intern_localtime, intern_local_offset,
  intern_civil, intern_new_offset, intern_merge, intern_BigDecimal;
static VALUE sym_symbolize_keys, sym_as, sym_array, sym_struct, sym_database_timezone,
  sym_application_timezone, sym_local, sym_utc, sym_cast_booleans,
  sym_cache_rows, sym_cast, sym_stream, sym_name;

/* internal resultAs constants */
#define AS_HASH   0
#define AS_ARRAY  1
#define AS_STRUCT 2

/* wrapper for intern.h:rb_struct_define() */
#define STRUCT_MAX_COLUMNS  100
static VALUE rb_mysql_struct_define2(const char *name, char **ary, my_ulonglong len);


/* Mark any VALUEs that are only referenced in C, so the GC won't get them. */
static void rb_mysql_result_mark(void * wrapper) {
  mysql2_result_wrapper * w = wrapper;
  if (w) {
    rb_gc_mark(w->fields);
    rb_gc_mark(w->rows);
    rb_gc_mark(w->encoding);
    rb_gc_mark(w->rowStruct);
    rb_gc_mark(w->client);
    rb_gc_mark(w->statement);
  }
}

/* this may be called manually or during GC */
static void rb_mysql_result_free_result(mysql2_result_wrapper * wrapper) {
  if (!wrapper) return;

  if (wrapper->resultFreed != 1) {
    if (wrapper->stmt_wrapper) {
      if (!wrapper->stmt_wrapper->closed) {
        mysql_stmt_free_result(wrapper->stmt_wrapper->stmt);

        /* MySQL BUG? If the statement handle was previously used, and so
         * mysql_stmt_bind_result was called, and if that result set and bind buffers were freed,
         * MySQL still thinks the result set buffer is available and will prefetch the
         * first result in mysql_stmt_execute. This will corrupt or crash the program.
         * By setting bind_result_done back to 0, we make MySQL think that a result set
         * has never been bound to this statement handle before to prevent the prefetch.
         */
        wrapper->stmt_wrapper->stmt->bind_result_done = 0;
      }

      if (wrapper->statement != Qnil) {
        decr_mysql2_stmt(wrapper->stmt_wrapper);
      }

      if (wrapper->result_buffers) {
        unsigned int i;
        for (i = 0; i < wrapper->numberOfFields; i++) {
          if (wrapper->result_buffers[i].buffer) {
            xfree(wrapper->result_buffers[i].buffer);
          }
        }
        xfree(wrapper->result_buffers);
        xfree(wrapper->is_null);
        xfree(wrapper->error);
        xfree(wrapper->length);
      }
      /* Clue that the next statement execute will need to allocate a new result buffer. */
      wrapper->result_buffers = NULL;
    }
    /* FIXME: this may call flush_use_result, which can hit the socket */
    /* For prepared statements, wrapper->result is the result metadata */
    mysql_free_result(wrapper->result);
    wrapper->resultFreed = 1;
  }
}

/* this is called during GC */
static void rb_mysql_result_free(void *ptr) {
  mysql2_result_wrapper *wrapper = ptr;
  rb_mysql_result_free_result(wrapper);

  // If the GC gets to client first it will be nil
  if (wrapper->client != Qnil) {
    decr_mysql2_client(wrapper->client_wrapper);
  }

  xfree(wrapper);
}

static VALUE rb_mysql_result_free_(VALUE self) {
  GET_RESULT(self);
  rb_mysql_result_free_result(wrapper);
  return Qnil;
}

/*
 * for small results, this won't hit the network, but there's no
 * reliable way for us to tell this so we'll always release the GVL
 * to be safe
 */
static void *nogvl_fetch_row(void *ptr) {
  MYSQL_RES *result = ptr;

  return mysql_fetch_row(result);
}

static void *nogvl_stmt_fetch(void *ptr) {
  MYSQL_STMT *stmt = ptr;
  uintptr_t r = mysql_stmt_fetch(stmt);

  return (void *)r;
}

static VALUE rb_mysql_result_fetch_field(VALUE self, unsigned int idx, int symbolize_keys) {
  VALUE rb_field;
  GET_RESULT(self);

  if (wrapper->fields == Qnil) {
    wrapper->numberOfFields = mysql_num_fields(wrapper->result);
    wrapper->fields = rb_ary_new2(wrapper->numberOfFields);
  }

  rb_field = rb_ary_entry(wrapper->fields, idx);
  if (rb_field == Qnil) {
    MYSQL_FIELD *field = NULL;
    rb_encoding *default_internal_enc = rb_default_internal_encoding();
    rb_encoding *conn_enc = rb_to_encoding(wrapper->encoding);

    field = mysql_fetch_field_direct(wrapper->result, idx);
    if (symbolize_keys) {
      rb_field = rb_intern3(field->name, field->name_length, rb_utf8_encoding());
      rb_field = ID2SYM(rb_field);
    } else {
      rb_field = rb_str_new(field->name, field->name_length);
      rb_enc_associate(rb_field, conn_enc);
      if (default_internal_enc) {
        rb_field = rb_str_export_to_enc(rb_field, default_internal_enc);
      }
    }
    rb_ary_store(wrapper->fields, idx, rb_field);
  }

  return rb_field;
}

static VALUE mysql2_set_field_string_encoding(VALUE val, MYSQL_FIELD field, rb_encoding *default_internal_enc, rb_encoding *conn_enc) {
  /* if binary flag is set, respect its wishes */
  if (field.flags & BINARY_FLAG && field.charsetnr == 63) {
    rb_enc_associate(val, binaryEncoding);
  } else if (!field.charsetnr) {
    /* MySQL 4.x may not provide an encoding, binary will get the bytes through */
    rb_enc_associate(val, binaryEncoding);
  } else {
    /* lookup the encoding configured on this field */
    const char *enc_name;
    int enc_index;

    enc_name = (field.charsetnr-1 < CHARSETNR_SIZE) ? mysql2_mysql_enc_to_rb[field.charsetnr-1] : NULL;
    
    if (enc_name != NULL) {
      /* use the field encoding we were able to match */
      enc_index = rb_enc_find_index(enc_name);
      rb_enc_set_index(val, enc_index);
    } else {
      /* otherwise fall-back to the connection's encoding */
      rb_enc_associate(val, conn_enc);
    }

    if (default_internal_enc) {
      val = rb_str_export_to_enc(val, default_internal_enc);
    }
  }
  return val;
}

/* Interpret microseconds digits left-aligned in fixed-width field.
 * e.g. 10.123 seconds means 10 seconds and 123000 microseconds,
 * because the microseconds are to the right of the decimal point.
 */
static unsigned int msec_char_to_uint(char *msec_char, size_t len)
{
  size_t i;
  for (i = 0; i < (len - 1); i++) {
    if (msec_char[i] == '\0') {
      msec_char[i] = '0';
    }
  }
  return (unsigned int)strtoul(msec_char, NULL, 10);
}

static void rb_mysql_result_alloc_result_buffers(VALUE self, MYSQL_FIELD *fields) {
  unsigned int i;
  GET_RESULT(self);

  if (wrapper->result_buffers != NULL) return;

  wrapper->result_buffers = xcalloc(wrapper->numberOfFields, sizeof(MYSQL_BIND));
  wrapper->is_null = xcalloc(wrapper->numberOfFields, sizeof(my_bool));
  wrapper->error = xcalloc(wrapper->numberOfFields, sizeof(my_bool));
  wrapper->length = xcalloc(wrapper->numberOfFields, sizeof(unsigned long));

  for (i = 0; i < wrapper->numberOfFields; i++) {
    wrapper->result_buffers[i].buffer_type = fields[i].type;

    //      mysql type    |            C type
    switch(fields[i].type) {
      case MYSQL_TYPE_NULL:         // NULL
        break;
      case MYSQL_TYPE_TINY:         // signed char
        wrapper->result_buffers[i].buffer = xcalloc(1, sizeof(signed char));
        wrapper->result_buffers[i].buffer_length = sizeof(signed char);
        break;
      case MYSQL_TYPE_SHORT:        // short int
      case MYSQL_TYPE_YEAR:         // short int
        wrapper->result_buffers[i].buffer = xcalloc(1, sizeof(short int));
        wrapper->result_buffers[i].buffer_length = sizeof(short int);
        break;
      case MYSQL_TYPE_INT24:        // int
      case MYSQL_TYPE_LONG:         // int
        wrapper->result_buffers[i].buffer = xcalloc(1, sizeof(int));
        wrapper->result_buffers[i].buffer_length = sizeof(int);
        break;
      case MYSQL_TYPE_LONGLONG:     // long long int
        wrapper->result_buffers[i].buffer = xcalloc(1, sizeof(long long int));
        wrapper->result_buffers[i].buffer_length = sizeof(long long int);
        break;
      case MYSQL_TYPE_FLOAT:        // float
      case MYSQL_TYPE_DOUBLE:       // double
        wrapper->result_buffers[i].buffer = xcalloc(1, sizeof(double));
        wrapper->result_buffers[i].buffer_length = sizeof(double);
        break;
      case MYSQL_TYPE_TIME:         // MYSQL_TIME
      case MYSQL_TYPE_DATE:         // MYSQL_TIME
      case MYSQL_TYPE_NEWDATE:      // MYSQL_TIME
      case MYSQL_TYPE_DATETIME:     // MYSQL_TIME
      case MYSQL_TYPE_TIMESTAMP:    // MYSQL_TIME
        wrapper->result_buffers[i].buffer = xcalloc(1, sizeof(MYSQL_TIME));
        wrapper->result_buffers[i].buffer_length = sizeof(MYSQL_TIME);
        break;
      case MYSQL_TYPE_DECIMAL:      // char[]
      case MYSQL_TYPE_NEWDECIMAL:   // char[]
      case MYSQL_TYPE_STRING:       // char[]
      case MYSQL_TYPE_VAR_STRING:   // char[]
      case MYSQL_TYPE_VARCHAR:      // char[]
      case MYSQL_TYPE_TINY_BLOB:    // char[]
      case MYSQL_TYPE_BLOB:         // char[]
      case MYSQL_TYPE_MEDIUM_BLOB:  // char[]
      case MYSQL_TYPE_LONG_BLOB:    // char[]
      case MYSQL_TYPE_BIT:          // char[]
      case MYSQL_TYPE_SET:          // char[]
      case MYSQL_TYPE_ENUM:         // char[]
      case MYSQL_TYPE_GEOMETRY:     // char[]
      default:
        wrapper->result_buffers[i].buffer = xmalloc(fields[i].max_length);
        wrapper->result_buffers[i].buffer_length = fields[i].max_length;
        break;
    }

    wrapper->result_buffers[i].is_null = &wrapper->is_null[i];
    wrapper->result_buffers[i].length  = &wrapper->length[i];
    wrapper->result_buffers[i].error   = &wrapper->error[i];
    wrapper->result_buffers[i].is_unsigned = ((fields[i].flags & UNSIGNED_FLAG) != 0);
  }
}

static VALUE rb_mysql_result_fetch_row_stmt(VALUE self, MYSQL_FIELD * fields, const result_each_args *args)
{
  VALUE rowVal;
  unsigned int i = 0;

  rb_encoding *default_internal_enc;
  rb_encoding *conn_enc;
  GET_RESULT(self);

  default_internal_enc = rb_default_internal_encoding();
  conn_enc = rb_to_encoding(wrapper->encoding);

  if (wrapper->fields == Qnil) {
    wrapper->numberOfFields = mysql_num_fields(wrapper->result);
    wrapper->fields = rb_ary_new2(wrapper->numberOfFields);
  }

  if (wrapper->result_buffers == NULL) {
    rb_mysql_result_alloc_result_buffers(self, fields);
  }

  if (mysql_stmt_bind_result(wrapper->stmt_wrapper->stmt, wrapper->result_buffers)) {
    rb_raise_mysql2_stmt_error(wrapper->stmt_wrapper);
  }

  {
    switch((uintptr_t)rb_thread_call_without_gvl(nogvl_stmt_fetch, wrapper->stmt_wrapper->stmt, RUBY_UBF_IO, 0)) {
      case 0:
        /* success */
        break;

      case 1:
        /* error */
        rb_raise_mysql2_stmt_error(wrapper->stmt_wrapper);

      case MYSQL_NO_DATA:
        /* no more row */
        return Qnil;

      case MYSQL_DATA_TRUNCATED:
        rb_raise(cMysql2Error, "IMPLBUG: caught MYSQL_DATA_TRUNCATED. should not come here as buffer_length is set to fields[i].max_length.");
    }
  }

  if (args->resultAs == AS_HASH) {
    rowVal = rb_hash_new();
  } else {
    rowVal = rb_ary_new2(wrapper->numberOfFields);
  }

  for (i = 0; i < wrapper->numberOfFields; i++) {
    VALUE field = rb_mysql_result_fetch_field(self, i, args->symbolizeKeys);
    VALUE val = Qnil;
    MYSQL_TIME *ts;

    if (wrapper->is_null[i]) {
      val = Qnil;
    } else {
      const MYSQL_BIND* const result_buffer = &wrapper->result_buffers[i];

      switch(result_buffer->buffer_type) {
        case MYSQL_TYPE_TINY:         // signed char
          if (args->castBool && fields[i].length == 1) {
            val = (*((unsigned char*)result_buffer->buffer) != 0) ? Qtrue : Qfalse;
            break;
          }
          if (result_buffer->is_unsigned) {
            val = UINT2NUM(*((unsigned char*)result_buffer->buffer));
          } else {
            val = INT2NUM(*((signed char*)result_buffer->buffer));
          }
          break;
        case MYSQL_TYPE_BIT:        /* BIT field (MySQL 5.0.3 and up) */
          if (args->castBool && fields[i].length == 1) {
            val = (*((unsigned char*)result_buffer->buffer) != 0) ? Qtrue : Qfalse;
          }else{
            val = rb_str_new(result_buffer->buffer, *(result_buffer->length));
          }
          break;
        case MYSQL_TYPE_SHORT:        // short int
        case MYSQL_TYPE_YEAR:         // short int
          if (result_buffer->is_unsigned) {
            val = UINT2NUM(*((unsigned short int*)result_buffer->buffer));
          } else  {
            val = INT2NUM(*((short int*)result_buffer->buffer));
          }
          break;
        case MYSQL_TYPE_INT24:        // int
        case MYSQL_TYPE_LONG:         // int
          if (result_buffer->is_unsigned) {
            val = UINT2NUM(*((unsigned int*)result_buffer->buffer));
          } else {
            val = INT2NUM(*((int*)result_buffer->buffer));
          }
          break;
        case MYSQL_TYPE_LONGLONG:     // long long int
          if (result_buffer->is_unsigned) {
            val = ULL2NUM(*((unsigned long long int*)result_buffer->buffer));
          } else {
            val = LL2NUM(*((long long int*)result_buffer->buffer));
          }
          break;
        case MYSQL_TYPE_FLOAT:        // float
          val = rb_float_new((double)(*((float*)result_buffer->buffer)));
          break;
        case MYSQL_TYPE_DOUBLE:       // double
          val = rb_float_new((double)(*((double*)result_buffer->buffer)));
          break;
        case MYSQL_TYPE_DATE:         // MYSQL_TIME
        case MYSQL_TYPE_NEWDATE:      // MYSQL_TIME
          ts = (MYSQL_TIME*)result_buffer->buffer;
          val = rb_funcall(cDate, intern_new, 3, INT2NUM(ts->year), INT2NUM(ts->month), INT2NUM(ts->day));
          break;
        case MYSQL_TYPE_TIME:         // MYSQL_TIME
          ts = (MYSQL_TIME*)result_buffer->buffer;
          val = rb_funcall(rb_cTime, args->db_timezone, 7, opt_time_year, opt_time_month, opt_time_month, UINT2NUM(ts->hour), UINT2NUM(ts->minute), UINT2NUM(ts->second), ULONG2NUM(ts->second_part));
          if (!NIL_P(args->app_timezone)) {
            if (args->app_timezone == intern_local) {
              val = rb_funcall(val, intern_localtime, 0);
            } else { // utc
              val = rb_funcall(val, intern_utc, 0);
            }
          }
          break;
        case MYSQL_TYPE_DATETIME:     // MYSQL_TIME
        case MYSQL_TYPE_TIMESTAMP: {  // MYSQL_TIME
          uint64_t seconds;

          ts = (MYSQL_TIME*)result_buffer->buffer;
          seconds = (ts->year*31557600ULL) + (ts->month*2592000ULL) + (ts->day*86400ULL) + (ts->hour*3600ULL) + (ts->minute*60ULL) + ts->second;

          if (seconds < MYSQL2_MIN_TIME || seconds > MYSQL2_MAX_TIME) { // use DateTime instead
            VALUE offset = INT2NUM(0);
            if (args->db_timezone == intern_local) {
              offset = rb_funcall(cMysql2Client, intern_local_offset, 0);
            }
            val = rb_funcall(cDateTime, intern_civil, 7, UINT2NUM(ts->year), UINT2NUM(ts->month), UINT2NUM(ts->day), UINT2NUM(ts->hour), UINT2NUM(ts->minute), UINT2NUM(ts->second), offset);
            if (!NIL_P(args->app_timezone)) {
              if (args->app_timezone == intern_local) {
                offset = rb_funcall(cMysql2Client, intern_local_offset, 0);
                val = rb_funcall(val, intern_new_offset, 1, offset);
              } else { // utc
                val = rb_funcall(val, intern_new_offset, 1, opt_utc_offset);
              }
            }
          } else {
            val = rb_funcall(rb_cTime, args->db_timezone, 7, UINT2NUM(ts->year), UINT2NUM(ts->month), UINT2NUM(ts->day), UINT2NUM(ts->hour), UINT2NUM(ts->minute), UINT2NUM(ts->second), ULONG2NUM(ts->second_part));
            if (!NIL_P(args->app_timezone)) {
              if (args->app_timezone == intern_local) {
                val = rb_funcall(val, intern_localtime, 0);
              } else { // utc
                val = rb_funcall(val, intern_utc, 0);
              }
            }
          }
          break;
        }
        case MYSQL_TYPE_DECIMAL:      // char[]
        case MYSQL_TYPE_NEWDECIMAL:   // char[]
          val = rb_funcall(rb_mKernel, intern_BigDecimal, 1, rb_str_new(result_buffer->buffer, *(result_buffer->length)));
          break;
        case MYSQL_TYPE_STRING:       // char[]
        case MYSQL_TYPE_VAR_STRING:   // char[]
        case MYSQL_TYPE_VARCHAR:      // char[]
        case MYSQL_TYPE_TINY_BLOB:    // char[]
        case MYSQL_TYPE_BLOB:         // char[]
        case MYSQL_TYPE_MEDIUM_BLOB:  // char[]
        case MYSQL_TYPE_LONG_BLOB:    // char[]
        case MYSQL_TYPE_SET:          // char[]
        case MYSQL_TYPE_ENUM:         // char[]
        case MYSQL_TYPE_GEOMETRY:     // char[]
        default:
          val = rb_str_new(result_buffer->buffer, *(result_buffer->length));
          val = mysql2_set_field_string_encoding(val, fields[i], default_internal_enc, conn_enc);
          break;
      }
    }

    if (args->resultAs == AS_HASH) {
      rb_hash_aset(rowVal, field, val);
    } else {
      rb_ary_push(rowVal, val);
    }
  }

  if (args->resultAs == AS_STRUCT) {
    if (wrapper->rowStruct == Qnil) {
      char *buf[STRUCT_MAX_COLUMNS];

      if (wrapper->numberOfFields > STRUCT_MAX_COLUMNS)
        rb_raise(cMysql2Error, "Too many struct fields: %llu", wrapper->numberOfFields);

      for (i = 0; i < wrapper->numberOfFields; i++) {
        VALUE field = rb_mysql_result_fetch_field(self, i, args->symbolizeKeys);
        buf[i] = StringValuePtr(field);
      }

      wrapper->rowStruct = rb_mysql_struct_define2(NULL, buf, wrapper->numberOfFields);
    }

    rowVal = rb_struct_alloc(wrapper->rowStruct, rowVal); 
  }

  return rowVal;
}

static VALUE rb_mysql_result_fetch_row(VALUE self, MYSQL_FIELD * fields, const result_each_args *args)
{
  VALUE rowVal;
  MYSQL_ROW row;
  unsigned int i = 0;
  unsigned long * fieldLengths;
  void * ptr;
  rb_encoding *default_internal_enc;
  rb_encoding *conn_enc;
  GET_RESULT(self);

  default_internal_enc = rb_default_internal_encoding();
  conn_enc = rb_to_encoding(wrapper->encoding);

  ptr = wrapper->result;
  row = (MYSQL_ROW)rb_thread_call_without_gvl(nogvl_fetch_row, ptr, RUBY_UBF_IO, 0);
  if (row == NULL) {
    return Qnil;
  }

  if (wrapper->fields == Qnil) {
    wrapper->numberOfFields = mysql_num_fields(wrapper->result);
    wrapper->fields = rb_ary_new2(wrapper->numberOfFields);
  }
  
  if (args->resultAs == AS_HASH) {
    rowVal = rb_hash_new();
  } else /* array or struct */ {
    /* struct uses array as an intermediary */
    rowVal = rb_ary_new2(wrapper->numberOfFields);
  }
  fieldLengths = mysql_fetch_lengths(wrapper->result);

  for (i = 0; i < wrapper->numberOfFields; i++) {
    VALUE field = rb_mysql_result_fetch_field(self, i, args->symbolizeKeys);
    if (row[i]) {
      VALUE val = Qnil;
      enum enum_field_types type = fields[i].type;

      if (!args->cast) {
        if (type == MYSQL_TYPE_NULL) {
          val = Qnil;
        } else {
          val = rb_str_new(row[i], fieldLengths[i]);
          val = mysql2_set_field_string_encoding(val, fields[i], default_internal_enc, conn_enc);
        }
      } else {
        switch (type) {
        case MYSQL_TYPE_NULL:       /* NULL-type field */
          val = Qnil;
          break;
        case MYSQL_TYPE_BIT:        /* BIT field (MySQL 5.0.3 and up) */
          if (args->castBool && fields[i].length == 1) {
            val = *row[i] == 1 ? Qtrue : Qfalse;
          } else {
            val = rb_str_new(row[i], fieldLengths[i]);
          }
          break;
        case MYSQL_TYPE_TINY:       /* TINYINT field */
          if (args->castBool && fields[i].length == 1) {
            val = *row[i] != '0' ? Qtrue : Qfalse;
            break;
          }
        case MYSQL_TYPE_SHORT:      /* SMALLINT field */
        case MYSQL_TYPE_LONG:       /* INTEGER field */
        case MYSQL_TYPE_INT24:      /* MEDIUMINT field */
        case MYSQL_TYPE_LONGLONG:   /* BIGINT field */
        case MYSQL_TYPE_YEAR:       /* YEAR field */
          val = rb_cstr2inum(row[i], 10);
          break;
        case MYSQL_TYPE_DECIMAL:    /* DECIMAL or NUMERIC field */
        case MYSQL_TYPE_NEWDECIMAL: /* Precision math DECIMAL or NUMERIC field (MySQL 5.0.3 and up) */
          if (fields[i].decimals == 0) {
            val = rb_cstr2inum(row[i], 10);
          } else if (strtod(row[i], NULL) == 0.000000) {
            val = rb_funcall(rb_mKernel, intern_BigDecimal, 1, opt_decimal_zero);
          } else {
            val = rb_funcall(rb_mKernel, intern_BigDecimal, 1, rb_str_new(row[i], fieldLengths[i]));
          }
          break;
        case MYSQL_TYPE_FLOAT:      /* FLOAT field */
        case MYSQL_TYPE_DOUBLE: {     /* DOUBLE or REAL field */
          double column_to_double;
          column_to_double = strtod(row[i], NULL);
          if (column_to_double == 0.000000){
            val = opt_float_zero;
          } else {
            val = rb_float_new(column_to_double);
          }
          break;
        }
        case MYSQL_TYPE_TIME: {     /* TIME field */
          int tokens;
          unsigned int hour=0, min=0, sec=0, msec=0;
          char msec_char[7] = {'0','0','0','0','0','0','\0'};

          tokens = sscanf(row[i], "%2u:%2u:%2u.%6s", &hour, &min, &sec, msec_char);
          if (tokens < 3) {
            val = Qnil;
            break;
          }
          msec = msec_char_to_uint(msec_char, sizeof(msec_char));
          val = rb_funcall(rb_cTime, args->db_timezone, 7, opt_time_year, opt_time_month, opt_time_month, UINT2NUM(hour), UINT2NUM(min), UINT2NUM(sec), UINT2NUM(msec));
          if (!NIL_P(args->app_timezone)) {
            if (args->app_timezone == intern_local) {
              val = rb_funcall(val, intern_localtime, 0);
            } else { /* utc */
              val = rb_funcall(val, intern_utc, 0);
            }
          }
          break;
        }
        case MYSQL_TYPE_TIMESTAMP:  /* TIMESTAMP field */
        case MYSQL_TYPE_DATETIME: { /* DATETIME field */
          int tokens;
          unsigned int year=0, month=0, day=0, hour=0, min=0, sec=0, msec=0;
          char msec_char[7] = {'0','0','0','0','0','0','\0'};
          uint64_t seconds;

          tokens = sscanf(row[i], "%4u-%2u-%2u %2u:%2u:%2u.%6s", &year, &month, &day, &hour, &min, &sec, msec_char);
          if (tokens < 6) { /* msec might be empty */
            val = Qnil;
            break;
          }
          seconds = (year*31557600ULL) + (month*2592000ULL) + (day*86400ULL) + (hour*3600ULL) + (min*60ULL) + sec;

          if (seconds == 0) {
            val = Qnil;
          } else {
            if (month < 1 || day < 1) {
              rb_raise(cMysql2Error, "Invalid date in field '%.*s': %s", fields[i].name_length, fields[i].name, row[i]);
              val = Qnil;
            } else {
              if (seconds < MYSQL2_MIN_TIME || seconds > MYSQL2_MAX_TIME) { /* use DateTime for larger date range, does not support microseconds */
                VALUE offset = INT2NUM(0);
                if (args->db_timezone == intern_local) {
                  offset = rb_funcall(cMysql2Client, intern_local_offset, 0);
                }
                val = rb_funcall(cDateTime, intern_civil, 7, UINT2NUM(year), UINT2NUM(month), UINT2NUM(day), UINT2NUM(hour), UINT2NUM(min), UINT2NUM(sec), offset);
                if (!NIL_P(args->app_timezone)) {
                  if (args->app_timezone == intern_local) {
                    offset = rb_funcall(cMysql2Client, intern_local_offset, 0);
                    val = rb_funcall(val, intern_new_offset, 1, offset);
                  } else { /* utc */
                    val = rb_funcall(val, intern_new_offset, 1, opt_utc_offset);
                  }
                }
              } else {
                msec = msec_char_to_uint(msec_char, sizeof(msec_char));
                val = rb_funcall(rb_cTime, args->db_timezone, 7, UINT2NUM(year), UINT2NUM(month), UINT2NUM(day), UINT2NUM(hour), UINT2NUM(min), UINT2NUM(sec), UINT2NUM(msec));
                if (!NIL_P(args->app_timezone)) {
                  if (args->app_timezone == intern_local) {
                    val = rb_funcall(val, intern_localtime, 0);
                  } else { /* utc */
                    val = rb_funcall(val, intern_utc, 0);
                  }
                }
              }
            }
          }
          break;
        }
        case MYSQL_TYPE_DATE:       /* DATE field */
        case MYSQL_TYPE_NEWDATE: {  /* Newer const used > 5.0 */
          int tokens;
          unsigned int year=0, month=0, day=0;
          tokens = sscanf(row[i], "%4u-%2u-%2u", &year, &month, &day);
          if (tokens < 3) {
            val = Qnil;
            break;
          }
          if (year+month+day == 0) {
            val = Qnil;
          } else {
            if (month < 1 || day < 1) {
              rb_raise(cMysql2Error, "Invalid date in field '%.*s': %s", fields[i].name_length, fields[i].name, row[i]);
              val = Qnil;
            } else {
              val = rb_funcall(cDate, intern_new, 3, UINT2NUM(year), UINT2NUM(month), UINT2NUM(day));
            }
          }
          break;
        }
        case MYSQL_TYPE_TINY_BLOB:
        case MYSQL_TYPE_MEDIUM_BLOB:
        case MYSQL_TYPE_LONG_BLOB:
        case MYSQL_TYPE_BLOB:
        case MYSQL_TYPE_VAR_STRING:
        case MYSQL_TYPE_VARCHAR:
        case MYSQL_TYPE_STRING:     /* CHAR or BINARY field */
        case MYSQL_TYPE_SET:        /* SET field */
        case MYSQL_TYPE_ENUM:       /* ENUM field */
        case MYSQL_TYPE_GEOMETRY:   /* Spatial fielda */
        default:
          val = rb_str_new(row[i], fieldLengths[i]);
          val = mysql2_set_field_string_encoding(val, fields[i], default_internal_enc, conn_enc);
          break;
        }
      }
      if (args->resultAs == AS_HASH) {
        rb_hash_aset(rowVal, field, val);
      } else /* array or struct */ {
        rb_ary_push(rowVal, val);
      }
    } else {
      if (args->resultAs == AS_HASH) {
        rb_hash_aset(rowVal, field, Qnil);
      } else /* array or struct */ {
        rb_ary_push(rowVal, Qnil);
      }
    }
  }

  /* turn intermediate array into struct */
  if (args->resultAs == AS_STRUCT) {
    if (wrapper->rowStruct == Qnil) {

/*
  idea: use rb_struct_s_def(int argc, VALUE *argv, VALUE klass) to create anonymous struct,
  the argvs must be pointers to symbols
  it's a mistake to use args->symbolizeKeys in rb_mysql_result_fetch_field call; it should always be true
 */
      char *buf[STRUCT_MAX_COLUMNS];

      if (wrapper->numberOfFields > STRUCT_MAX_COLUMNS)
        rb_raise(cMysql2Error, "Too many struct fields: %llu", wrapper->numberOfFields);

      for (i = 0; i < wrapper->numberOfFields; i++) {
        VALUE field = rb_mysql_result_fetch_field(self, i, args->symbolizeKeys);
        buf[i] = StringValuePtr(field);
      }

      wrapper->rowStruct = rb_mysql_struct_define2(NULL, buf, wrapper->numberOfFields);
    }

    rowVal = rb_struct_alloc(wrapper->rowStruct, rowVal); 
  }

  return rowVal;
}

static VALUE rb_mysql_result_fetch_fields(VALUE self) {
  unsigned int i = 0;
  short int symbolizeKeys = 0;
  VALUE defaults;

  GET_RESULT(self);

  defaults = rb_iv_get(self, "@query_options");
  Check_Type(defaults, T_HASH);
  if (rb_hash_aref(defaults, sym_symbolize_keys) == Qtrue) {
    symbolizeKeys = 1;
  }

  if (wrapper->fields == Qnil) {
    wrapper->numberOfFields = mysql_num_fields(wrapper->result);
    wrapper->fields = rb_ary_new2(wrapper->numberOfFields);
  }

  if ((my_ulonglong)RARRAY_LEN(wrapper->fields) != wrapper->numberOfFields) {
    for (i=0; i<wrapper->numberOfFields; i++) {
      rb_mysql_result_fetch_field(self, i, symbolizeKeys);
    }
  }

  return wrapper->fields;
}

static VALUE rb_mysql_result_each_(VALUE self,
                                   VALUE(*fetch_row_func)(VALUE, MYSQL_FIELD *fields, const result_each_args *args),
                                   const result_each_args *args)
{
  unsigned long i;
  const char *errstr;
  MYSQL_FIELD *fields = NULL;

  GET_RESULT(self);

  if (wrapper->is_streaming) {
    /* When streaming, we will only yield rows, not return them. */
    if (wrapper->rows == Qnil) {
      wrapper->rows = rb_ary_new();
    }

    if (!wrapper->streamingComplete) {
      VALUE row;

      fields = mysql_fetch_fields(wrapper->result);

      do {
        row = fetch_row_func(self, fields, args);
        if (row != Qnil) {
          wrapper->numberOfRows++;
          if (args->block_given != Qnil) {
            rb_yield(row);
          }
        }
      } while(row != Qnil);

      rb_mysql_result_free_result(wrapper);
      wrapper->streamingComplete = 1;

      // Check for errors, the connection might have gone out from under us
      // mysql_error returns an empty string if there is no error
      errstr = mysql_error(wrapper->client_wrapper->client);
      if (errstr[0]) {
        rb_raise(cMysql2Error, "%s", errstr);
      }
    } else {
      rb_raise(cMysql2Error, "You have already fetched all the rows for this query and streaming is true. (to reiterate you must requery).");
    }
  } else {
    if (args->cacheRows && wrapper->lastRowProcessed == wrapper->numberOfRows) {
      /* we've already read the entire dataset from the C result into our */
      /* internal array. Lets hand that over to the user since it's ready to go */
      for (i = 0; i < wrapper->numberOfRows; i++) {
        rb_yield(rb_ary_entry(wrapper->rows, i));
      }
    } else {
      unsigned long rowsProcessed = 0;
      rowsProcessed = RARRAY_LEN(wrapper->rows);
      fields = mysql_fetch_fields(wrapper->result);

      for (i = 0; i < wrapper->numberOfRows; i++) {
        VALUE row;
        if (args->cacheRows && i < rowsProcessed) {
          row = rb_ary_entry(wrapper->rows, i);
        } else {
          row = fetch_row_func(self, fields, args);
          if (args->cacheRows) {
            rb_ary_store(wrapper->rows, i, row);
          }
          wrapper->lastRowProcessed++;
        }

        if (row == Qnil) {
          /* we don't need the mysql C dataset around anymore, peace it */
          if (args->cacheRows) {
            rb_mysql_result_free_result(wrapper);
          }
          return Qnil;
        }

        if (args->block_given != Qnil) {
          rb_yield(row);
        }
      }
      if (wrapper->lastRowProcessed == wrapper->numberOfRows && args->cacheRows) {
        /* we don't need the mysql C dataset around anymore, peace it */
        rb_mysql_result_free_result(wrapper);
      }
    }
  }

  // FIXME return Enumerator instead?
  // return rb_ary_each(wrapper->rows);
  return wrapper->rows;
}

static VALUE rb_mysql_result_each(int argc, VALUE * argv, VALUE self) {
  result_each_args args;
  VALUE defaults, opts, block, (*fetch_row_func)(VALUE, MYSQL_FIELD *fields, const result_each_args *args);
  ID db_timezone, app_timezone, dbTz, appTz;
  int symbolizeKeys, resultAs, castBool, cacheRows, cast;

  GET_RESULT(self);

  if (wrapper->stmt_wrapper && wrapper->stmt_wrapper->closed) {
    rb_raise(cMysql2Error, "Statement handle already closed");
  }

  defaults = rb_iv_get(self, "@query_options");
  Check_Type(defaults, T_HASH);
  if (rb_scan_args(argc, argv, "01&", &opts, &block) == 1) {
    opts = rb_funcall(defaults, intern_merge, 1, opts);
  } else {
    opts = defaults;
  }

  symbolizeKeys = RTEST(rb_hash_aref(opts, sym_symbolize_keys));
  resultAs      = AS_HASH;
  castBool      = RTEST(rb_hash_aref(opts, sym_cast_booleans));
  cacheRows     = RTEST(rb_hash_aref(opts, sym_cache_rows));
  cast          = RTEST(rb_hash_aref(opts, sym_cast));

  if (rb_hash_aref(opts, sym_as) == sym_array) {
    resultAs = AS_ARRAY;
  } else if (rb_hash_aref(opts, sym_as) == sym_struct) {
    resultAs = AS_STRUCT;
  }

  if (wrapper->is_streaming && cacheRows) {
    rb_warn(":cache_rows is ignored if :stream is true");
  }

  if (wrapper->stmt_wrapper && !cacheRows && !wrapper->is_streaming) {
    rb_warn(":cache_rows is forced for prepared statements (if not streaming)");
    cacheRows = 1;
  }

  if (wrapper->stmt_wrapper && !cast) {
    rb_warn(":cast is forced for prepared statements");
  }

  dbTz = rb_hash_aref(opts, sym_database_timezone);
  if (dbTz == sym_local) {
    db_timezone = intern_local;
  } else if (dbTz == sym_utc) {
    db_timezone = intern_utc;
  } else {
    if (!NIL_P(dbTz)) {
      rb_warn(":database_timezone option must be :utc or :local - defaulting to :local");
    }
    db_timezone = intern_local;
  }

  appTz = rb_hash_aref(opts, sym_application_timezone);
  if (appTz == sym_local) {
    app_timezone = intern_local;
  } else if (appTz == sym_utc) {
    app_timezone = intern_utc;
  } else {
    app_timezone = Qnil;
  }

  if (wrapper->rows == Qnil && !wrapper->is_streaming) {
    wrapper->numberOfRows = wrapper->stmt_wrapper ? mysql_stmt_num_rows(wrapper->stmt_wrapper->stmt) : mysql_num_rows(wrapper->result);
    wrapper->rows = rb_ary_new2(wrapper->numberOfRows);
  } else if (wrapper->rows && !cacheRows) {
    if (wrapper->resultFreed) {
      rb_raise(cMysql2Error, "Result set has already been freed");
    }
    mysql_data_seek(wrapper->result, 0);
    wrapper->lastRowProcessed = 0;
    wrapper->rows = rb_ary_new2(wrapper->numberOfRows);
  }

  // Backward compat
  args.symbolizeKeys = symbolizeKeys;
  args.resultAs = resultAs;
  args.castBool = castBool;
  args.cacheRows = cacheRows;
  args.cast = cast;
  args.db_timezone = db_timezone;
  args.app_timezone = app_timezone;
  args.block_given = block;

  if (wrapper->stmt_wrapper) {
    fetch_row_func = rb_mysql_result_fetch_row_stmt;
  } else {
    fetch_row_func = rb_mysql_result_fetch_row;
  }

  return rb_mysql_result_each_(self, fetch_row_func, &args);
}

static VALUE rb_mysql_result_count(VALUE self) {
  GET_RESULT(self);

  if (wrapper->is_streaming) {
    /* This is an unsigned long per result.h */
    return ULONG2NUM(wrapper->numberOfRows);
  }

  if (wrapper->resultFreed) {
    /* Ruby arrays have platform signed long length */
    return LONG2NUM(RARRAY_LEN(wrapper->rows));
  } else {
    /* MySQL returns an unsigned 64-bit long here */
    if (wrapper->stmt_wrapper) {
      return ULL2NUM(mysql_stmt_num_rows(wrapper->stmt_wrapper->stmt));
    } else {
      return ULL2NUM(mysql_num_rows(wrapper->result));
    }
  }
}

/* Mysql2::Result */
VALUE rb_mysql_result_to_obj(VALUE client, VALUE encoding, VALUE options, MYSQL_RES *r, VALUE statement) {
  VALUE obj;
  mysql2_result_wrapper * wrapper;

  obj = Data_Make_Struct(cMysql2Result, mysql2_result_wrapper, rb_mysql_result_mark, rb_mysql_result_free, wrapper);
  wrapper->numberOfFields = 0;
  wrapper->numberOfRows = 0;
  wrapper->lastRowProcessed = 0;
  wrapper->resultFreed = 0;
  wrapper->result = r;
  wrapper->fields = Qnil;
  wrapper->rows = Qnil;
  wrapper->rowStruct = Qnil;
  wrapper->encoding = encoding;
  wrapper->streamingComplete = 0;
  wrapper->client = client;
  wrapper->client_wrapper = DATA_PTR(client);
  wrapper->client_wrapper->refcount++;
  wrapper->result_buffers = NULL;
  wrapper->is_null = NULL;
  wrapper->error = NULL;
  wrapper->length = NULL;

  /* Keep a handle to the Statement to ensure it doesn't get garbage collected first */
  wrapper->statement = statement;
  if (statement != Qnil) {
    wrapper->stmt_wrapper = DATA_PTR(statement);
    wrapper->stmt_wrapper->refcount++;
  } else {
    wrapper->stmt_wrapper = NULL;
  }

  rb_obj_call_init(obj, 0, NULL);
  rb_iv_set(obj, "@query_options", options);

  /* Options that cannot be changed in results.each(...) { |row| }
   * should be processed here. */
  wrapper->is_streaming = (rb_hash_aref(options, sym_stream) == Qtrue ? 1 : 0);

  return obj;
}

void init_mysql2_result() {
  cDate = rb_const_get(rb_cObject, rb_intern("Date"));
  cDateTime = rb_const_get(rb_cObject, rb_intern("DateTime"));

  cMysql2Result = rb_define_class_under(mMysql2, "Result", rb_cObject);
  rb_define_method(cMysql2Result, "each", rb_mysql_result_each, -1);
  rb_define_method(cMysql2Result, "fields", rb_mysql_result_fetch_fields, 0);
  rb_define_method(cMysql2Result, "free", rb_mysql_result_free_, 0);
  rb_define_method(cMysql2Result, "count", rb_mysql_result_count, 0);
  rb_define_alias(cMysql2Result, "size", "count");

  intern_new          = rb_intern("new");
  intern_utc          = rb_intern("utc");
  intern_local        = rb_intern("local");
  intern_merge        = rb_intern("merge");
  intern_localtime    = rb_intern("localtime");
  intern_local_offset = rb_intern("local_offset");
  intern_civil        = rb_intern("civil");
  intern_new_offset   = rb_intern("new_offset");
  intern_BigDecimal   = rb_intern("BigDecimal");

  sym_symbolize_keys  = ID2SYM(rb_intern("symbolize_keys"));
  sym_as              = ID2SYM(rb_intern("as"));
  sym_array           = ID2SYM(rb_intern("array"));
  sym_struct          = ID2SYM(rb_intern("struct"));
  sym_local           = ID2SYM(rb_intern("local"));
  sym_utc             = ID2SYM(rb_intern("utc"));
  sym_cast_booleans   = ID2SYM(rb_intern("cast_booleans"));
  sym_database_timezone     = ID2SYM(rb_intern("database_timezone"));
  sym_application_timezone  = ID2SYM(rb_intern("application_timezone"));
  sym_cache_rows      = ID2SYM(rb_intern("cache_rows"));
  sym_cast            = ID2SYM(rb_intern("cast"));
  sym_stream          = ID2SYM(rb_intern("stream"));
  sym_name            = ID2SYM(rb_intern("name"));

  opt_decimal_zero = rb_str_new2("0.0");
  rb_global_variable(&opt_decimal_zero); /*never GC */
  opt_float_zero = rb_float_new((double)0);
  rb_global_variable(&opt_float_zero);
  opt_time_year = INT2NUM(2000);
  opt_time_month = INT2NUM(1);
  opt_utc_offset = INT2NUM(0);

  binaryEncoding = rb_enc_find("binary");
}

/*
# Ruby snippet to create the switch statement below.
def xxx
    return (1..STRUCT_MAX_COLUMNS).collect do |i|
        "  case #{i}:\n    st = rb_struct_define(name, " + 
        i.times.collect {|a| "ary[#{a}], "}.join +
        "NULL);\n    break;\n"
    end.join
end
*/

/*
  Wrapper for intern.h:rb_struct_define().
  Takes array, len of the fields in the struct. Works around rb_struct_define()'s use of varargs.
  Stopping at 100 because fuck.
 */
static VALUE rb_mysql_struct_define2(const char *name, char **ary, my_ulonglong len) {
  VALUE st;

  switch (len) {
  case 1:
    st = rb_struct_define(name, ary[0], NULL);
    break;
  case 2:
    st = rb_struct_define(name, ary[0], ary[1], NULL);
    break;
  case 3:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], NULL);
    break;
  case 4:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], NULL);
    break;
  case 5:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], NULL);
    break;
  case 6:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], NULL);
    break;
  case 7:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], NULL);
    break;
  case 8:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], NULL);
    break;
  case 9:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], NULL);
    break;
  case 10:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], NULL);
    break;  
  case 11:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], NULL);
    break;
  case 12:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], NULL);
    break;
  case 13:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], NULL);
    break;
  case 14:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], NULL);
    break;
  case 15:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], NULL);
    break;
  case 16:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], NULL);
    break;
  case 17:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], NULL);
    break;
  case 18:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], NULL);
    break;
  case 19:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], NULL);
    break;
  case 20:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], ary[19], NULL);
    break;
  case 21:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], ary[19], ary[20], NULL);
    break;
  case 22:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], ary[19], ary[20], ary[21], NULL);
    break;
  case 23:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], ary[19], ary[20], ary[21], ary[22], NULL);
    break;
  case 24:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], ary[19], ary[20], ary[21], ary[22], ary[23], NULL);
    break;
  case 25:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], ary[19], ary[20], ary[21], ary[22], ary[23], ary[24], NULL);
    break;
  case 26:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], ary[19], ary[20], ary[21], ary[22], ary[23], ary[24], ary[25], NULL);
    break;
  case 27:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], ary[19], ary[20], ary[21], ary[22], ary[23], ary[24], ary[25], ary[26], NULL);
    break;
  case 28:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], ary[19], ary[20], ary[21], ary[22], ary[23], ary[24], ary[25], ary[26], ary[27], NULL);
    break;
  case 29:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], ary[19], ary[20], ary[21], ary[22], ary[23], ary[24], ary[25], ary[26], ary[27], ary[28], NULL);
    break;
  case 30:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], ary[19], ary[20], ary[21], ary[22], ary[23], ary[24], ary[25], ary[26], ary[27], ary[28], ary[29], NULL);
    break;
  case 31:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], ary[19], ary[20], ary[21], ary[22], ary[23], ary[24], ary[25], ary[26], ary[27], ary[28], ary[29], ary[30], NULL);
    break;
  case 32:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], ary[19], ary[20], ary[21], ary[22], ary[23], ary[24], ary[25], ary[26], ary[27], ary[28], ary[29], ary[30], ary[31], NULL);
    break;
  case 33:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], ary[19], ary[20], ary[21], ary[22], ary[23], ary[24], ary[25], ary[26], ary[27], ary[28], ary[29], ary[30], ary[31], ary[32], NULL);
    break;
  case 34:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], ary[19], ary[20], ary[21], ary[22], ary[23], ary[24], ary[25], ary[26], ary[27], ary[28], ary[29], ary[30], ary[31], ary[32], ary[33], NULL);
    break;
  case 35:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], ary[19], ary[20], ary[21], ary[22], ary[23], ary[24], ary[25], ary[26], ary[27], ary[28], ary[29], ary[30], ary[31], ary[32], ary[33], ary[34], NULL);
    break;
  case 36:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], ary[19], ary[20], ary[21], ary[22], ary[23], ary[24], ary[25], ary[26], ary[27], ary[28], ary[29], ary[30], ary[31], ary[32], ary[33], ary[34], ary[35], NULL);
    break;
  case 37:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], ary[19], ary[20], ary[21], ary[22], ary[23], ary[24], ary[25], ary[26], ary[27], ary[28], ary[29], ary[30], ary[31], ary[32], ary[33], ary[34], ary[35], ary[36], NULL);
    break;
  case 38:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], ary[19], ary[20], ary[21], ary[22], ary[23], ary[24], ary[25], ary[26], ary[27], ary[28], ary[29], ary[30], ary[31], ary[32], ary[33], ary[34], ary[35], ary[36], ary[37], NULL);
    break;
  case 39:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], ary[19], ary[20], ary[21], ary[22], ary[23], ary[24], ary[25], ary[26], ary[27], ary[28], ary[29], ary[30], ary[31], ary[32], ary[33], ary[34], ary[35], ary[36], ary[37], ary[38], NULL);
    break;
  case 40:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], ary[19], ary[20], ary[21], ary[22], ary[23], ary[24], ary[25], ary[26], ary[27], ary[28], ary[29], ary[30], ary[31], ary[32], ary[33], ary[34], ary[35], ary[36], ary[37], ary[38], ary[39], NULL);
    break;
  case 41:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], ary[19], ary[20], ary[21], ary[22], ary[23], ary[24], ary[25], ary[26], ary[27], ary[28], ary[29], ary[30], ary[31], ary[32], ary[33], ary[34], ary[35], ary[36], ary[37], ary[38], ary[39], ary[40], NULL);
    break;
  case 42:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], ary[19], ary[20], ary[21], ary[22], ary[23], ary[24], ary[25], ary[26], ary[27], ary[28], ary[29], ary[30], ary[31], ary[32], ary[33], ary[34], ary[35], ary[36], ary[37], ary[38], ary[39], ary[40], ary[41], NULL);
    break;
  case 43:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], ary[19], ary[20], ary[21], ary[22], ary[23], ary[24], ary[25], ary[26], ary[27], ary[28], ary[29], ary[30], ary[31], ary[32], ary[33], ary[34], ary[35], ary[36], ary[37], ary[38], ary[39], ary[40], ary[41], ary[42], NULL);
    break;
  case 44:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], ary[19], ary[20], ary[21], ary[22], ary[23], ary[24], ary[25], ary[26], ary[27], ary[28], ary[29], ary[30], ary[31], ary[32], ary[33], ary[34], ary[35], ary[36], ary[37], ary[38], ary[39], ary[40], ary[41], ary[42], ary[43], NULL);
    break;
  case 45:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], ary[19], ary[20], ary[21], ary[22], ary[23], ary[24], ary[25], ary[26], ary[27], ary[28], ary[29], ary[30], ary[31], ary[32], ary[33], ary[34], ary[35], ary[36], ary[37], ary[38], ary[39], ary[40], ary[41], ary[42], ary[43], ary[44], NULL);
    break;
  case 46:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], ary[19], ary[20], ary[21], ary[22], ary[23], ary[24], ary[25], ary[26], ary[27], ary[28], ary[29], ary[30], ary[31], ary[32], ary[33], ary[34], ary[35], ary[36], ary[37], ary[38], ary[39], ary[40], ary[41], ary[42], ary[43], ary[44], ary[45], NULL);
    break;
  case 47:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], ary[19], ary[20], ary[21], ary[22], ary[23], ary[24], ary[25], ary[26], ary[27], ary[28], ary[29], ary[30], ary[31], ary[32], ary[33], ary[34], ary[35], ary[36], ary[37], ary[38], ary[39], ary[40], ary[41], ary[42], ary[43], ary[44], ary[45], ary[46], NULL);
    break;
  case 48:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], ary[19], ary[20], ary[21], ary[22], ary[23], ary[24], ary[25], ary[26], ary[27], ary[28], ary[29], ary[30], ary[31], ary[32], ary[33], ary[34], ary[35], ary[36], ary[37], ary[38], ary[39], ary[40], ary[41], ary[42], ary[43], ary[44], ary[45], ary[46], ary[47], NULL);
    break;
  case 49:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], ary[19], ary[20], ary[21], ary[22], ary[23], ary[24], ary[25], ary[26], ary[27], ary[28], ary[29], ary[30], ary[31], ary[32], ary[33], ary[34], ary[35], ary[36], ary[37], ary[38], ary[39], ary[40], ary[41], ary[42], ary[43], ary[44], ary[45], ary[46], ary[47], ary[48], NULL);
    break;
  case 50:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], ary[19], ary[20], ary[21], ary[22], ary[23], ary[24], ary[25], ary[26], ary[27], ary[28], ary[29], ary[30], ary[31], ary[32], ary[33], ary[34], ary[35], ary[36], ary[37], ary[38], ary[39], ary[40], ary[41], ary[42], ary[43], ary[44], ary[45], ary[46], ary[47], ary[48], ary[49], NULL);
    break;
  case 51:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], ary[19], ary[20], ary[21], ary[22], ary[23], ary[24], ary[25], ary[26], ary[27], ary[28], ary[29], ary[30], ary[31], ary[32], ary[33], ary[34], ary[35], ary[36], ary[37], ary[38], ary[39], ary[40], ary[41], ary[42], ary[43], ary[44], ary[45], ary[46], ary[47], ary[48], ary[49], ary[50], NULL);
    break;
  case 52:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], ary[19], ary[20], ary[21], ary[22], ary[23], ary[24], ary[25], ary[26], ary[27], ary[28], ary[29], ary[30], ary[31], ary[32], ary[33], ary[34], ary[35], ary[36], ary[37], ary[38], ary[39], ary[40], ary[41], ary[42], ary[43], ary[44], ary[45], ary[46], ary[47], ary[48], ary[49], ary[50], ary[51], NULL);
    break;
  case 53:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], ary[19], ary[20], ary[21], ary[22], ary[23], ary[24], ary[25], ary[26], ary[27], ary[28], ary[29], ary[30], ary[31], ary[32], ary[33], ary[34], ary[35], ary[36], ary[37], ary[38], ary[39], ary[40], ary[41], ary[42], ary[43], ary[44], ary[45], ary[46], ary[47], ary[48], ary[49], ary[50], ary[51], ary[52], NULL);
    break;
  case 54:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], ary[19], ary[20], ary[21], ary[22], ary[23], ary[24], ary[25], ary[26], ary[27], ary[28], ary[29], ary[30], ary[31], ary[32], ary[33], ary[34], ary[35], ary[36], ary[37], ary[38], ary[39], ary[40], ary[41], ary[42], ary[43], ary[44], ary[45], ary[46], ary[47], ary[48], ary[49], ary[50], ary[51], ary[52], ary[53], NULL);
    break;
  case 55:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], ary[19], ary[20], ary[21], ary[22], ary[23], ary[24], ary[25], ary[26], ary[27], ary[28], ary[29], ary[30], ary[31], ary[32], ary[33], ary[34], ary[35], ary[36], ary[37], ary[38], ary[39], ary[40], ary[41], ary[42], ary[43], ary[44], ary[45], ary[46], ary[47], ary[48], ary[49], ary[50], ary[51], ary[52], ary[53], ary[54], NULL);
    break;
  case 56:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], ary[19], ary[20], ary[21], ary[22], ary[23], ary[24], ary[25], ary[26], ary[27], ary[28], ary[29], ary[30], ary[31], ary[32], ary[33], ary[34], ary[35], ary[36], ary[37], ary[38], ary[39], ary[40], ary[41], ary[42], ary[43], ary[44], ary[45], ary[46], ary[47], ary[48], ary[49], ary[50], ary[51], ary[52], ary[53], ary[54], ary[55], NULL);
    break;
  case 57:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], ary[19], ary[20], ary[21], ary[22], ary[23], ary[24], ary[25], ary[26], ary[27], ary[28], ary[29], ary[30], ary[31], ary[32], ary[33], ary[34], ary[35], ary[36], ary[37], ary[38], ary[39], ary[40], ary[41], ary[42], ary[43], ary[44], ary[45], ary[46], ary[47], ary[48], ary[49], ary[50], ary[51], ary[52], ary[53], ary[54], ary[55], ary[56], NULL);
    break;
  case 58:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], ary[19], ary[20], ary[21], ary[22], ary[23], ary[24], ary[25], ary[26], ary[27], ary[28], ary[29], ary[30], ary[31], ary[32], ary[33], ary[34], ary[35], ary[36], ary[37], ary[38], ary[39], ary[40], ary[41], ary[42], ary[43], ary[44], ary[45], ary[46], ary[47], ary[48], ary[49], ary[50], ary[51], ary[52], ary[53], ary[54], ary[55], ary[56], ary[57], NULL);
    break;
  case 59:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], ary[19], ary[20], ary[21], ary[22], ary[23], ary[24], ary[25], ary[26], ary[27], ary[28], ary[29], ary[30], ary[31], ary[32], ary[33], ary[34], ary[35], ary[36], ary[37], ary[38], ary[39], ary[40], ary[41], ary[42], ary[43], ary[44], ary[45], ary[46], ary[47], ary[48], ary[49], ary[50], ary[51], ary[52], ary[53], ary[54], ary[55], ary[56], ary[57], ary[58], NULL);
    break;
  case 60:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], ary[19], ary[20], ary[21], ary[22], ary[23], ary[24], ary[25], ary[26], ary[27], ary[28], ary[29], ary[30], ary[31], ary[32], ary[33], ary[34], ary[35], ary[36], ary[37], ary[38], ary[39], ary[40], ary[41], ary[42], ary[43], ary[44], ary[45], ary[46], ary[47], ary[48], ary[49], ary[50], ary[51], ary[52], ary[53], ary[54], ary[55], ary[56], ary[57], ary[58], ary[59], NULL);
    break;
  case 61:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], ary[19], ary[20], ary[21], ary[22], ary[23], ary[24], ary[25], ary[26], ary[27], ary[28], ary[29], ary[30], ary[31], ary[32], ary[33], ary[34], ary[35], ary[36], ary[37], ary[38], ary[39], ary[40], ary[41], ary[42], ary[43], ary[44], ary[45], ary[46], ary[47], ary[48], ary[49], ary[50], ary[51], ary[52], ary[53], ary[54], ary[55], ary[56], ary[57], ary[58], ary[59], ary[60], NULL);
    break;
  case 62:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], ary[19], ary[20], ary[21], ary[22], ary[23], ary[24], ary[25], ary[26], ary[27], ary[28], ary[29], ary[30], ary[31], ary[32], ary[33], ary[34], ary[35], ary[36], ary[37], ary[38], ary[39], ary[40], ary[41], ary[42], ary[43], ary[44], ary[45], ary[46], ary[47], ary[48], ary[49], ary[50], ary[51], ary[52], ary[53], ary[54], ary[55], ary[56], ary[57], ary[58], ary[59], ary[60], ary[61], NULL);
    break;
  case 63:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], ary[19], ary[20], ary[21], ary[22], ary[23], ary[24], ary[25], ary[26], ary[27], ary[28], ary[29], ary[30], ary[31], ary[32], ary[33], ary[34], ary[35], ary[36], ary[37], ary[38], ary[39], ary[40], ary[41], ary[42], ary[43], ary[44], ary[45], ary[46], ary[47], ary[48], ary[49], ary[50], ary[51], ary[52], ary[53], ary[54], ary[55], ary[56], ary[57], ary[58], ary[59], ary[60], ary[61], ary[62], NULL);
    break;
  case 64:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], ary[19], ary[20], ary[21], ary[22], ary[23], ary[24], ary[25], ary[26], ary[27], ary[28], ary[29], ary[30], ary[31], ary[32], ary[33], ary[34], ary[35], ary[36], ary[37], ary[38], ary[39], ary[40], ary[41], ary[42], ary[43], ary[44], ary[45], ary[46], ary[47], ary[48], ary[49], ary[50], ary[51], ary[52], ary[53], ary[54], ary[55], ary[56], ary[57], ary[58], ary[59], ary[60], ary[61], ary[62], ary[63], NULL);
    break;
  case 65:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], ary[19], ary[20], ary[21], ary[22], ary[23], ary[24], ary[25], ary[26], ary[27], ary[28], ary[29], ary[30], ary[31], ary[32], ary[33], ary[34], ary[35], ary[36], ary[37], ary[38], ary[39], ary[40], ary[41], ary[42], ary[43], ary[44], ary[45], ary[46], ary[47], ary[48], ary[49], ary[50], ary[51], ary[52], ary[53], ary[54], ary[55], ary[56], ary[57], ary[58], ary[59], ary[60], ary[61], ary[62], ary[63], ary[64], NULL);
    break;
  case 66:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], ary[19], ary[20], ary[21], ary[22], ary[23], ary[24], ary[25], ary[26], ary[27], ary[28], ary[29], ary[30], ary[31], ary[32], ary[33], ary[34], ary[35], ary[36], ary[37], ary[38], ary[39], ary[40], ary[41], ary[42], ary[43], ary[44], ary[45], ary[46], ary[47], ary[48], ary[49], ary[50], ary[51], ary[52], ary[53], ary[54], ary[55], ary[56], ary[57], ary[58], ary[59], ary[60], ary[61], ary[62], ary[63], ary[64], ary[65], NULL);
    break;
  case 67:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], ary[19], ary[20], ary[21], ary[22], ary[23], ary[24], ary[25], ary[26], ary[27], ary[28], ary[29], ary[30], ary[31], ary[32], ary[33], ary[34], ary[35], ary[36], ary[37], ary[38], ary[39], ary[40], ary[41], ary[42], ary[43], ary[44], ary[45], ary[46], ary[47], ary[48], ary[49], ary[50], ary[51], ary[52], ary[53], ary[54], ary[55], ary[56], ary[57], ary[58], ary[59], ary[60], ary[61], ary[62], ary[63], ary[64], ary[65], ary[66], NULL);
    break;
  case 68:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], ary[19], ary[20], ary[21], ary[22], ary[23], ary[24], ary[25], ary[26], ary[27], ary[28], ary[29], ary[30], ary[31], ary[32], ary[33], ary[34], ary[35], ary[36], ary[37], ary[38], ary[39], ary[40], ary[41], ary[42], ary[43], ary[44], ary[45], ary[46], ary[47], ary[48], ary[49], ary[50], ary[51], ary[52], ary[53], ary[54], ary[55], ary[56], ary[57], ary[58], ary[59], ary[60], ary[61], ary[62], ary[63], ary[64], ary[65], ary[66], ary[67], NULL);
    break;
  case 69:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], ary[19], ary[20], ary[21], ary[22], ary[23], ary[24], ary[25], ary[26], ary[27], ary[28], ary[29], ary[30], ary[31], ary[32], ary[33], ary[34], ary[35], ary[36], ary[37], ary[38], ary[39], ary[40], ary[41], ary[42], ary[43], ary[44], ary[45], ary[46], ary[47], ary[48], ary[49], ary[50], ary[51], ary[52], ary[53], ary[54], ary[55], ary[56], ary[57], ary[58], ary[59], ary[60], ary[61], ary[62], ary[63], ary[64], ary[65], ary[66], ary[67], ary[68], NULL);
    break;
  case 70:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], ary[19], ary[20], ary[21], ary[22], ary[23], ary[24], ary[25], ary[26], ary[27], ary[28], ary[29], ary[30], ary[31], ary[32], ary[33], ary[34], ary[35], ary[36], ary[37], ary[38], ary[39], ary[40], ary[41], ary[42], ary[43], ary[44], ary[45], ary[46], ary[47], ary[48], ary[49], ary[50], ary[51], ary[52], ary[53], ary[54], ary[55], ary[56], ary[57], ary[58], ary[59], ary[60], ary[61], ary[62], ary[63], ary[64], ary[65], ary[66], ary[67], ary[68], ary[69], NULL);
    break;
  case 71:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], ary[19], ary[20], ary[21], ary[22], ary[23], ary[24], ary[25], ary[26], ary[27], ary[28], ary[29], ary[30], ary[31], ary[32], ary[33], ary[34], ary[35], ary[36], ary[37], ary[38], ary[39], ary[40], ary[41], ary[42], ary[43], ary[44], ary[45], ary[46], ary[47], ary[48], ary[49], ary[50], ary[51], ary[52], ary[53], ary[54], ary[55], ary[56], ary[57], ary[58], ary[59], ary[60], ary[61], ary[62], ary[63], ary[64], ary[65], ary[66], ary[67], ary[68], ary[69], ary[70], NULL);
    break;
  case 72:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], ary[19], ary[20], ary[21], ary[22], ary[23], ary[24], ary[25], ary[26], ary[27], ary[28], ary[29], ary[30], ary[31], ary[32], ary[33], ary[34], ary[35], ary[36], ary[37], ary[38], ary[39], ary[40], ary[41], ary[42], ary[43], ary[44], ary[45], ary[46], ary[47], ary[48], ary[49], ary[50], ary[51], ary[52], ary[53], ary[54], ary[55], ary[56], ary[57], ary[58], ary[59], ary[60], ary[61], ary[62], ary[63], ary[64], ary[65], ary[66], ary[67], ary[68], ary[69], ary[70], ary[71], NULL);
    break;
  case 73:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], ary[19], ary[20], ary[21], ary[22], ary[23], ary[24], ary[25], ary[26], ary[27], ary[28], ary[29], ary[30], ary[31], ary[32], ary[33], ary[34], ary[35], ary[36], ary[37], ary[38], ary[39], ary[40], ary[41], ary[42], ary[43], ary[44], ary[45], ary[46], ary[47], ary[48], ary[49], ary[50], ary[51], ary[52], ary[53], ary[54], ary[55], ary[56], ary[57], ary[58], ary[59], ary[60], ary[61], ary[62], ary[63], ary[64], ary[65], ary[66], ary[67], ary[68], ary[69], ary[70], ary[71], ary[72], NULL);
    break;
  case 74:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], ary[19], ary[20], ary[21], ary[22], ary[23], ary[24], ary[25], ary[26], ary[27], ary[28], ary[29], ary[30], ary[31], ary[32], ary[33], ary[34], ary[35], ary[36], ary[37], ary[38], ary[39], ary[40], ary[41], ary[42], ary[43], ary[44], ary[45], ary[46], ary[47], ary[48], ary[49], ary[50], ary[51], ary[52], ary[53], ary[54], ary[55], ary[56], ary[57], ary[58], ary[59], ary[60], ary[61], ary[62], ary[63], ary[64], ary[65], ary[66], ary[67], ary[68], ary[69], ary[70], ary[71], ary[72], ary[73], NULL);
    break;
  case 75:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], ary[19], ary[20], ary[21], ary[22], ary[23], ary[24], ary[25], ary[26], ary[27], ary[28], ary[29], ary[30], ary[31], ary[32], ary[33], ary[34], ary[35], ary[36], ary[37], ary[38], ary[39], ary[40], ary[41], ary[42], ary[43], ary[44], ary[45], ary[46], ary[47], ary[48], ary[49], ary[50], ary[51], ary[52], ary[53], ary[54], ary[55], ary[56], ary[57], ary[58], ary[59], ary[60], ary[61], ary[62], ary[63], ary[64], ary[65], ary[66], ary[67], ary[68], ary[69], ary[70], ary[71], ary[72], ary[73], ary[74], NULL);
    break;
  case 76:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], ary[19], ary[20], ary[21], ary[22], ary[23], ary[24], ary[25], ary[26], ary[27], ary[28], ary[29], ary[30], ary[31], ary[32], ary[33], ary[34], ary[35], ary[36], ary[37], ary[38], ary[39], ary[40], ary[41], ary[42], ary[43], ary[44], ary[45], ary[46], ary[47], ary[48], ary[49], ary[50], ary[51], ary[52], ary[53], ary[54], ary[55], ary[56], ary[57], ary[58], ary[59], ary[60], ary[61], ary[62], ary[63], ary[64], ary[65], ary[66], ary[67], ary[68], ary[69], ary[70], ary[71], ary[72], ary[73], ary[74], ary[75], NULL);
    break;
  case 77:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], ary[19], ary[20], ary[21], ary[22], ary[23], ary[24], ary[25], ary[26], ary[27], ary[28], ary[29], ary[30], ary[31], ary[32], ary[33], ary[34], ary[35], ary[36], ary[37], ary[38], ary[39], ary[40], ary[41], ary[42], ary[43], ary[44], ary[45], ary[46], ary[47], ary[48], ary[49], ary[50], ary[51], ary[52], ary[53], ary[54], ary[55], ary[56], ary[57], ary[58], ary[59], ary[60], ary[61], ary[62], ary[63], ary[64], ary[65], ary[66], ary[67], ary[68], ary[69], ary[70], ary[71], ary[72], ary[73], ary[74], ary[75], ary[76], NULL);
    break;
  case 78:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], ary[19], ary[20], ary[21], ary[22], ary[23], ary[24], ary[25], ary[26], ary[27], ary[28], ary[29], ary[30], ary[31], ary[32], ary[33], ary[34], ary[35], ary[36], ary[37], ary[38], ary[39], ary[40], ary[41], ary[42], ary[43], ary[44], ary[45], ary[46], ary[47], ary[48], ary[49], ary[50], ary[51], ary[52], ary[53], ary[54], ary[55], ary[56], ary[57], ary[58], ary[59], ary[60], ary[61], ary[62], ary[63], ary[64], ary[65], ary[66], ary[67], ary[68], ary[69], ary[70], ary[71], ary[72], ary[73], ary[74], ary[75], ary[76], ary[77], NULL);
    break;
  case 79:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], ary[19], ary[20], ary[21], ary[22], ary[23], ary[24], ary[25], ary[26], ary[27], ary[28], ary[29], ary[30], ary[31], ary[32], ary[33], ary[34], ary[35], ary[36], ary[37], ary[38], ary[39], ary[40], ary[41], ary[42], ary[43], ary[44], ary[45], ary[46], ary[47], ary[48], ary[49], ary[50], ary[51], ary[52], ary[53], ary[54], ary[55], ary[56], ary[57], ary[58], ary[59], ary[60], ary[61], ary[62], ary[63], ary[64], ary[65], ary[66], ary[67], ary[68], ary[69], ary[70], ary[71], ary[72], ary[73], ary[74], ary[75], ary[76], ary[77], ary[78], NULL);
    break;
  case 80:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], ary[19], ary[20], ary[21], ary[22], ary[23], ary[24], ary[25], ary[26], ary[27], ary[28], ary[29], ary[30], ary[31], ary[32], ary[33], ary[34], ary[35], ary[36], ary[37], ary[38], ary[39], ary[40], ary[41], ary[42], ary[43], ary[44], ary[45], ary[46], ary[47], ary[48], ary[49], ary[50], ary[51], ary[52], ary[53], ary[54], ary[55], ary[56], ary[57], ary[58], ary[59], ary[60], ary[61], ary[62], ary[63], ary[64], ary[65], ary[66], ary[67], ary[68], ary[69], ary[70], ary[71], ary[72], ary[73], ary[74], ary[75], ary[76], ary[77], ary[78], ary[79], NULL);
    break;
  case 81:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], ary[19], ary[20], ary[21], ary[22], ary[23], ary[24], ary[25], ary[26], ary[27], ary[28], ary[29], ary[30], ary[31], ary[32], ary[33], ary[34], ary[35], ary[36], ary[37], ary[38], ary[39], ary[40], ary[41], ary[42], ary[43], ary[44], ary[45], ary[46], ary[47], ary[48], ary[49], ary[50], ary[51], ary[52], ary[53], ary[54], ary[55], ary[56], ary[57], ary[58], ary[59], ary[60], ary[61], ary[62], ary[63], ary[64], ary[65], ary[66], ary[67], ary[68], ary[69], ary[70], ary[71], ary[72], ary[73], ary[74], ary[75], ary[76], ary[77], ary[78], ary[79], ary[80], NULL);
    break;
  case 82:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], ary[19], ary[20], ary[21], ary[22], ary[23], ary[24], ary[25], ary[26], ary[27], ary[28], ary[29], ary[30], ary[31], ary[32], ary[33], ary[34], ary[35], ary[36], ary[37], ary[38], ary[39], ary[40], ary[41], ary[42], ary[43], ary[44], ary[45], ary[46], ary[47], ary[48], ary[49], ary[50], ary[51], ary[52], ary[53], ary[54], ary[55], ary[56], ary[57], ary[58], ary[59], ary[60], ary[61], ary[62], ary[63], ary[64], ary[65], ary[66], ary[67], ary[68], ary[69], ary[70], ary[71], ary[72], ary[73], ary[74], ary[75], ary[76], ary[77], ary[78], ary[79], ary[80], ary[81], NULL);
    break;
  case 83:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], ary[19], ary[20], ary[21], ary[22], ary[23], ary[24], ary[25], ary[26], ary[27], ary[28], ary[29], ary[30], ary[31], ary[32], ary[33], ary[34], ary[35], ary[36], ary[37], ary[38], ary[39], ary[40], ary[41], ary[42], ary[43], ary[44], ary[45], ary[46], ary[47], ary[48], ary[49], ary[50], ary[51], ary[52], ary[53], ary[54], ary[55], ary[56], ary[57], ary[58], ary[59], ary[60], ary[61], ary[62], ary[63], ary[64], ary[65], ary[66], ary[67], ary[68], ary[69], ary[70], ary[71], ary[72], ary[73], ary[74], ary[75], ary[76], ary[77], ary[78], ary[79], ary[80], ary[81], ary[82], NULL);
    break;
  case 84:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], ary[19], ary[20], ary[21], ary[22], ary[23], ary[24], ary[25], ary[26], ary[27], ary[28], ary[29], ary[30], ary[31], ary[32], ary[33], ary[34], ary[35], ary[36], ary[37], ary[38], ary[39], ary[40], ary[41], ary[42], ary[43], ary[44], ary[45], ary[46], ary[47], ary[48], ary[49], ary[50], ary[51], ary[52], ary[53], ary[54], ary[55], ary[56], ary[57], ary[58], ary[59], ary[60], ary[61], ary[62], ary[63], ary[64], ary[65], ary[66], ary[67], ary[68], ary[69], ary[70], ary[71], ary[72], ary[73], ary[74], ary[75], ary[76], ary[77], ary[78], ary[79], ary[80], ary[81], ary[82], ary[83], NULL);
    break;
  case 85:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], ary[19], ary[20], ary[21], ary[22], ary[23], ary[24], ary[25], ary[26], ary[27], ary[28], ary[29], ary[30], ary[31], ary[32], ary[33], ary[34], ary[35], ary[36], ary[37], ary[38], ary[39], ary[40], ary[41], ary[42], ary[43], ary[44], ary[45], ary[46], ary[47], ary[48], ary[49], ary[50], ary[51], ary[52], ary[53], ary[54], ary[55], ary[56], ary[57], ary[58], ary[59], ary[60], ary[61], ary[62], ary[63], ary[64], ary[65], ary[66], ary[67], ary[68], ary[69], ary[70], ary[71], ary[72], ary[73], ary[74], ary[75], ary[76], ary[77], ary[78], ary[79], ary[80], ary[81], ary[82], ary[83], ary[84], NULL);
    break;
  case 86:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], ary[19], ary[20], ary[21], ary[22], ary[23], ary[24], ary[25], ary[26], ary[27], ary[28], ary[29], ary[30], ary[31], ary[32], ary[33], ary[34], ary[35], ary[36], ary[37], ary[38], ary[39], ary[40], ary[41], ary[42], ary[43], ary[44], ary[45], ary[46], ary[47], ary[48], ary[49], ary[50], ary[51], ary[52], ary[53], ary[54], ary[55], ary[56], ary[57], ary[58], ary[59], ary[60], ary[61], ary[62], ary[63], ary[64], ary[65], ary[66], ary[67], ary[68], ary[69], ary[70], ary[71], ary[72], ary[73], ary[74], ary[75], ary[76], ary[77], ary[78], ary[79], ary[80], ary[81], ary[82], ary[83], ary[84], ary[85], NULL);
    break;
  case 87:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], ary[19], ary[20], ary[21], ary[22], ary[23], ary[24], ary[25], ary[26], ary[27], ary[28], ary[29], ary[30], ary[31], ary[32], ary[33], ary[34], ary[35], ary[36], ary[37], ary[38], ary[39], ary[40], ary[41], ary[42], ary[43], ary[44], ary[45], ary[46], ary[47], ary[48], ary[49], ary[50], ary[51], ary[52], ary[53], ary[54], ary[55], ary[56], ary[57], ary[58], ary[59], ary[60], ary[61], ary[62], ary[63], ary[64], ary[65], ary[66], ary[67], ary[68], ary[69], ary[70], ary[71], ary[72], ary[73], ary[74], ary[75], ary[76], ary[77], ary[78], ary[79], ary[80], ary[81], ary[82], ary[83], ary[84], ary[85], ary[86], NULL);
    break;
  case 88:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], ary[19], ary[20], ary[21], ary[22], ary[23], ary[24], ary[25], ary[26], ary[27], ary[28], ary[29], ary[30], ary[31], ary[32], ary[33], ary[34], ary[35], ary[36], ary[37], ary[38], ary[39], ary[40], ary[41], ary[42], ary[43], ary[44], ary[45], ary[46], ary[47], ary[48], ary[49], ary[50], ary[51], ary[52], ary[53], ary[54], ary[55], ary[56], ary[57], ary[58], ary[59], ary[60], ary[61], ary[62], ary[63], ary[64], ary[65], ary[66], ary[67], ary[68], ary[69], ary[70], ary[71], ary[72], ary[73], ary[74], ary[75], ary[76], ary[77], ary[78], ary[79], ary[80], ary[81], ary[82], ary[83], ary[84], ary[85], ary[86], ary[87], NULL);
    break;
  case 89:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], ary[19], ary[20], ary[21], ary[22], ary[23], ary[24], ary[25], ary[26], ary[27], ary[28], ary[29], ary[30], ary[31], ary[32], ary[33], ary[34], ary[35], ary[36], ary[37], ary[38], ary[39], ary[40], ary[41], ary[42], ary[43], ary[44], ary[45], ary[46], ary[47], ary[48], ary[49], ary[50], ary[51], ary[52], ary[53], ary[54], ary[55], ary[56], ary[57], ary[58], ary[59], ary[60], ary[61], ary[62], ary[63], ary[64], ary[65], ary[66], ary[67], ary[68], ary[69], ary[70], ary[71], ary[72], ary[73], ary[74], ary[75], ary[76], ary[77], ary[78], ary[79], ary[80], ary[81], ary[82], ary[83], ary[84], ary[85], ary[86], ary[87], ary[88], NULL);
    break;
  case 90:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], ary[19], ary[20], ary[21], ary[22], ary[23], ary[24], ary[25], ary[26], ary[27], ary[28], ary[29], ary[30], ary[31], ary[32], ary[33], ary[34], ary[35], ary[36], ary[37], ary[38], ary[39], ary[40], ary[41], ary[42], ary[43], ary[44], ary[45], ary[46], ary[47], ary[48], ary[49], ary[50], ary[51], ary[52], ary[53], ary[54], ary[55], ary[56], ary[57], ary[58], ary[59], ary[60], ary[61], ary[62], ary[63], ary[64], ary[65], ary[66], ary[67], ary[68], ary[69], ary[70], ary[71], ary[72], ary[73], ary[74], ary[75], ary[76], ary[77], ary[78], ary[79], ary[80], ary[81], ary[82], ary[83], ary[84], ary[85], ary[86], ary[87], ary[88], ary[89], NULL);
    break;
  case 91:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], ary[19], ary[20], ary[21], ary[22], ary[23], ary[24], ary[25], ary[26], ary[27], ary[28], ary[29], ary[30], ary[31], ary[32], ary[33], ary[34], ary[35], ary[36], ary[37], ary[38], ary[39], ary[40], ary[41], ary[42], ary[43], ary[44], ary[45], ary[46], ary[47], ary[48], ary[49], ary[50], ary[51], ary[52], ary[53], ary[54], ary[55], ary[56], ary[57], ary[58], ary[59], ary[60], ary[61], ary[62], ary[63], ary[64], ary[65], ary[66], ary[67], ary[68], ary[69], ary[70], ary[71], ary[72], ary[73], ary[74], ary[75], ary[76], ary[77], ary[78], ary[79], ary[80], ary[81], ary[82], ary[83], ary[84], ary[85], ary[86], ary[87], ary[88], ary[89], ary[90], NULL);
    break;
  case 92:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], ary[19], ary[20], ary[21], ary[22], ary[23], ary[24], ary[25], ary[26], ary[27], ary[28], ary[29], ary[30], ary[31], ary[32], ary[33], ary[34], ary[35], ary[36], ary[37], ary[38], ary[39], ary[40], ary[41], ary[42], ary[43], ary[44], ary[45], ary[46], ary[47], ary[48], ary[49], ary[50], ary[51], ary[52], ary[53], ary[54], ary[55], ary[56], ary[57], ary[58], ary[59], ary[60], ary[61], ary[62], ary[63], ary[64], ary[65], ary[66], ary[67], ary[68], ary[69], ary[70], ary[71], ary[72], ary[73], ary[74], ary[75], ary[76], ary[77], ary[78], ary[79], ary[80], ary[81], ary[82], ary[83], ary[84], ary[85], ary[86], ary[87], ary[88], ary[89], ary[90], ary[91], NULL);
    break;
  case 93:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], ary[19], ary[20], ary[21], ary[22], ary[23], ary[24], ary[25], ary[26], ary[27], ary[28], ary[29], ary[30], ary[31], ary[32], ary[33], ary[34], ary[35], ary[36], ary[37], ary[38], ary[39], ary[40], ary[41], ary[42], ary[43], ary[44], ary[45], ary[46], ary[47], ary[48], ary[49], ary[50], ary[51], ary[52], ary[53], ary[54], ary[55], ary[56], ary[57], ary[58], ary[59], ary[60], ary[61], ary[62], ary[63], ary[64], ary[65], ary[66], ary[67], ary[68], ary[69], ary[70], ary[71], ary[72], ary[73], ary[74], ary[75], ary[76], ary[77], ary[78], ary[79], ary[80], ary[81], ary[82], ary[83], ary[84], ary[85], ary[86], ary[87], ary[88], ary[89], ary[90], ary[91], ary[92], NULL);
    break;
  case 94:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], ary[19], ary[20], ary[21], ary[22], ary[23], ary[24], ary[25], ary[26], ary[27], ary[28], ary[29], ary[30], ary[31], ary[32], ary[33], ary[34], ary[35], ary[36], ary[37], ary[38], ary[39], ary[40], ary[41], ary[42], ary[43], ary[44], ary[45], ary[46], ary[47], ary[48], ary[49], ary[50], ary[51], ary[52], ary[53], ary[54], ary[55], ary[56], ary[57], ary[58], ary[59], ary[60], ary[61], ary[62], ary[63], ary[64], ary[65], ary[66], ary[67], ary[68], ary[69], ary[70], ary[71], ary[72], ary[73], ary[74], ary[75], ary[76], ary[77], ary[78], ary[79], ary[80], ary[81], ary[82], ary[83], ary[84], ary[85], ary[86], ary[87], ary[88], ary[89], ary[90], ary[91], ary[92], ary[93], NULL);
    break;
  case 95:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], ary[19], ary[20], ary[21], ary[22], ary[23], ary[24], ary[25], ary[26], ary[27], ary[28], ary[29], ary[30], ary[31], ary[32], ary[33], ary[34], ary[35], ary[36], ary[37], ary[38], ary[39], ary[40], ary[41], ary[42], ary[43], ary[44], ary[45], ary[46], ary[47], ary[48], ary[49], ary[50], ary[51], ary[52], ary[53], ary[54], ary[55], ary[56], ary[57], ary[58], ary[59], ary[60], ary[61], ary[62], ary[63], ary[64], ary[65], ary[66], ary[67], ary[68], ary[69], ary[70], ary[71], ary[72], ary[73], ary[74], ary[75], ary[76], ary[77], ary[78], ary[79], ary[80], ary[81], ary[82], ary[83], ary[84], ary[85], ary[86], ary[87], ary[88], ary[89], ary[90], ary[91], ary[92], ary[93], ary[94], NULL);
    break;
  case 96:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], ary[19], ary[20], ary[21], ary[22], ary[23], ary[24], ary[25], ary[26], ary[27], ary[28], ary[29], ary[30], ary[31], ary[32], ary[33], ary[34], ary[35], ary[36], ary[37], ary[38], ary[39], ary[40], ary[41], ary[42], ary[43], ary[44], ary[45], ary[46], ary[47], ary[48], ary[49], ary[50], ary[51], ary[52], ary[53], ary[54], ary[55], ary[56], ary[57], ary[58], ary[59], ary[60], ary[61], ary[62], ary[63], ary[64], ary[65], ary[66], ary[67], ary[68], ary[69], ary[70], ary[71], ary[72], ary[73], ary[74], ary[75], ary[76], ary[77], ary[78], ary[79], ary[80], ary[81], ary[82], ary[83], ary[84], ary[85], ary[86], ary[87], ary[88], ary[89], ary[90], ary[91], ary[92], ary[93], ary[94], ary[95], NULL);
    break;
  case 97:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], ary[19], ary[20], ary[21], ary[22], ary[23], ary[24], ary[25], ary[26], ary[27], ary[28], ary[29], ary[30], ary[31], ary[32], ary[33], ary[34], ary[35], ary[36], ary[37], ary[38], ary[39], ary[40], ary[41], ary[42], ary[43], ary[44], ary[45], ary[46], ary[47], ary[48], ary[49], ary[50], ary[51], ary[52], ary[53], ary[54], ary[55], ary[56], ary[57], ary[58], ary[59], ary[60], ary[61], ary[62], ary[63], ary[64], ary[65], ary[66], ary[67], ary[68], ary[69], ary[70], ary[71], ary[72], ary[73], ary[74], ary[75], ary[76], ary[77], ary[78], ary[79], ary[80], ary[81], ary[82], ary[83], ary[84], ary[85], ary[86], ary[87], ary[88], ary[89], ary[90], ary[91], ary[92], ary[93], ary[94], ary[95], ary[96], NULL);
    break;
  case 98:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], ary[19], ary[20], ary[21], ary[22], ary[23], ary[24], ary[25], ary[26], ary[27], ary[28], ary[29], ary[30], ary[31], ary[32], ary[33], ary[34], ary[35], ary[36], ary[37], ary[38], ary[39], ary[40], ary[41], ary[42], ary[43], ary[44], ary[45], ary[46], ary[47], ary[48], ary[49], ary[50], ary[51], ary[52], ary[53], ary[54], ary[55], ary[56], ary[57], ary[58], ary[59], ary[60], ary[61], ary[62], ary[63], ary[64], ary[65], ary[66], ary[67], ary[68], ary[69], ary[70], ary[71], ary[72], ary[73], ary[74], ary[75], ary[76], ary[77], ary[78], ary[79], ary[80], ary[81], ary[82], ary[83], ary[84], ary[85], ary[86], ary[87], ary[88], ary[89], ary[90], ary[91], ary[92], ary[93], ary[94], ary[95], ary[96], ary[97], NULL);
    break;
  case 99:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], ary[19], ary[20], ary[21], ary[22], ary[23], ary[24], ary[25], ary[26], ary[27], ary[28], ary[29], ary[30], ary[31], ary[32], ary[33], ary[34], ary[35], ary[36], ary[37], ary[38], ary[39], ary[40], ary[41], ary[42], ary[43], ary[44], ary[45], ary[46], ary[47], ary[48], ary[49], ary[50], ary[51], ary[52], ary[53], ary[54], ary[55], ary[56], ary[57], ary[58], ary[59], ary[60], ary[61], ary[62], ary[63], ary[64], ary[65], ary[66], ary[67], ary[68], ary[69], ary[70], ary[71], ary[72], ary[73], ary[74], ary[75], ary[76], ary[77], ary[78], ary[79], ary[80], ary[81], ary[82], ary[83], ary[84], ary[85], ary[86], ary[87], ary[88], ary[89], ary[90], ary[91], ary[92], ary[93], ary[94], ary[95], ary[96], ary[97], ary[98], NULL);
    break;
  case 100:
    st = rb_struct_define(name, ary[0], ary[1], ary[2], ary[3], ary[4], ary[5], ary[6], ary[7], ary[8], ary[9], ary[10], ary[11], ary[12], ary[13], ary[14], ary[15], ary[16], ary[17], ary[18], ary[19], ary[20], ary[21], ary[22], ary[23], ary[24], ary[25], ary[26], ary[27], ary[28], ary[29], ary[30], ary[31], ary[32], ary[33], ary[34], ary[35], ary[36], ary[37], ary[38], ary[39], ary[40], ary[41], ary[42], ary[43], ary[44], ary[45], ary[46], ary[47], ary[48], ary[49], ary[50], ary[51], ary[52], ary[53], ary[54], ary[55], ary[56], ary[57], ary[58], ary[59], ary[60], ary[61], ary[62], ary[63], ary[64], ary[65], ary[66], ary[67], ary[68], ary[69], ary[70], ary[71], ary[72], ary[73], ary[74], ary[75], ary[76], ary[77], ary[78], ary[79], ary[80], ary[81], ary[82], ary[83], ary[84], ary[85], ary[86], ary[87], ary[88], ary[89], ary[90], ary[91], ary[92], ary[93], ary[94], ary[95], ary[96], ary[97], ary[98], ary[99], NULL);
    break;
  default:
    st = Qnil;
  }

  return st;
}
