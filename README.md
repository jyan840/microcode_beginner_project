# microcode_beginner_project

## Instructions:

```
(opcode 000)  load  address      :  ACC <- memory[ address ]

(opcode 001)  add   address      :  ACC <- ACC + memory[ address ]

(opcode 010)  store address      :  memory[ address ] <- ACC

(opcode 011)  brz   address      :  if( ACC == 0 ) PC <- address

(opcode 100)  strcpy source dest :  memory[ dest ] <- memory[ source .. \0 ] 
100. xxxxxx yyyyyyy
```

## `strcpy`

* [ ] Modify instruction decode for new `strcpy` opcode (3-bits wide).
* [ ] Modify instruction decode for `strcpy` arguments
      (two 6-bit wide addresses).
* [ ] Implement control for `strcpy`.
    * Start on paper first!

### Example:

```
before memory:
00: ----


f0: ffff
  : ffff
  : 0000

after memory:
00: ffff
  : ffff
  : 0000

f0: ffff
  : ffff
  : 0000

strcpy f0 00
==> ACC <- mem[f0]
==> mem[00] <- ACC
==> ACC <- mem[fX]
==> mem[0X] <-- ACC
==> ...
```
