/*
 * backwards compatibility for Rubinius. See
 * https://github.com/rubinius/rubinius/issues/3771.
 *
 * Ruby 1.9.3 provides this API which allows the use of ppoll() on Linux
 * to minimize select() and malloc() overhead on high-numbered FDs.
 */
#ifdef HAVE_RB_WAIT_FOR_SINGLE_FD
#  include <ruby/io.h>
#else
#  define RB_WAITFD_IN  0x001
#  define RB_WAITFD_PRI 0x002
#  define RB_WAITFD_OUT 0x004

static int my_wait_for_single_fd(int fd, int events, struct timeval *tvp)
{
  fd_set fdset;
  fd_set *rfds;
  fd_set *wfds;
  fd_set *efds;
  int retval;

  for (;;) {
    FD_ZERO(&fdset);
    FD_SET(fd, &fdset);

    rfds = (events & RB_WAITFD_IN)  ? &fdset : NULL;
    wfds = (events & RB_WAITFD_OUT) ? &fdset : NULL;
    efds = (events & RB_WAITFD_PRI) ? &fdset : NULL;

    retval = rb_thread_select(fd + 1, rfds, wfds, efds, tvp);
    /* work around bug in 1.8.7-p374 scheduler that sometimes returns timeout when it shouldn't */
    /* https://www.ruby-forum.com/topic/194009 */

    if (retval || tvp)
      break;
  }
  return retval;
}

#define rb_wait_for_single_fd(fd,events,tvp) \
        my_wait_for_single_fd((fd),(events),(tvp))
#endif