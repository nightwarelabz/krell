/* Window-size shim for the krell_core example.
 *
 * The example asks the terminal for its size through this
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
 *    pointer and fail. Compiled C knows each platform's
 *    convention, so the query goes through this wrapper on
 *    every platform.
 */
#include <sys/ioctl.h>

int kc_winsize(int fd, void *ws)
{
    return ioctl(fd, TIOCGWINSZ, (struct winsize *)ws);
}
