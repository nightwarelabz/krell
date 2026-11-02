/* Window-size shim for the fullscreen terminal examples.
 *
 * The examples ask the terminal for its size through this
 * fixed-argument wrapper instead of calling ioctl() directly.
 * Two reasons:
 *
 * 1. The TIOCGWINSZ request value lives in the platform header
 *    (<sys/ioctl.h>), not in the program. The same Krell module
 *    runs on every platform; the request number does not.
 *
 * 2. ioctl() is variadic in C, and Darwin's ARM64 convention
 *    passes variadic arguments on the stack, not in registers.
 *    Krell's backend emits the standard register call, which is
 *    correct for Linux but makes Darwin's ioctl read a garbage
 *    pointer. Compiled C knows each platform's convention, so
 *    the query goes through this wrapper on every platform.
 *
 * The buffer is seeded with 80x24 before the query, so a failed
 * query leaves a sane default instead of uninitialized memory.
 */
#include <sys/ioctl.h>

int kc_winsize(int fd, void *ws)
{
    struct winsize *w = (struct winsize *)ws;
    w->ws_row = 24;
    w->ws_col = 80;
    return ioctl(fd, TIOCGWINSZ, w);
}
