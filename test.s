[bits 64]
section .text
global _start
plus:
add RDI, RSI
mov RAX, RDI
ret
_start:
mov RBX, 2
mov RDI, RBX
mov RBX, 3
mov RSI, RBX
mov RDI, RSI
mov RAX, 60
syscall
