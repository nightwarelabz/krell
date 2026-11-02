/\.type /d
/\.size /d
/GNU-stack/d
s/^\.section \.rodata$/.section __TEXT,__const/
s/:lo12:([A-Za-z0-9_.]+)/\1@PAGEOFF/g
s/(adrp x[0-9]+, )([A-Za-z0-9_.]+)$/\1\2@PAGE/
s/bl (write|ioctl|usleep|malloc|free|sin|cos|sqrt|kc_winsize)$/bl _\1/
s/\.globl main$/.globl _main/
s/^main:/_main:/
