/* Non-variadic window-size query for macOS / Linux.
 *
 * ioctl() is variadic in C, and Darwin's ARM64 convention passes
 * variadic arguments on the stack, not in registers. Krell's
 * backend emits the standard AAPCS64 register call, which is
 * correct for Linux but makes Darwin's ioctl read a garbage
 * pointer. This fixed-argument wrapper is compiled by clang,
 * which knows the Darwin convention, so the query lands. */
#include <sys/ioctl.h>
#include <unistd.h>

int kc_winsize(int fd, void *ws)
{
    struct winsize *w = (struct winsize *)ws;
    w->ws_row = 24;
    w->ws_col = 80;
    return ioctl(fd, TIOCGWINSZ, w);
}
