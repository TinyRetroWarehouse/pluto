.section .text
entry:
    mov $0xCAFE, %eax
    mov $0xBEEF, %ebx
loop:
    jmp loop

