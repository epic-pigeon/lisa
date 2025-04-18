# LiSA tutorials

This repository contains the code developed and used during LiSA's tutorials. Every tutorial is listed together with a link to the slides used and the tag of the code shown during the tutorial itself.

## Tutorials given

- PLDI '24 [[slides]](https://docs.google.com/presentation/d/1-oFl5Lgg-6mu0IdXMv8u-9w_ypc1aYbg-t_t8HVQBjw/edit?usp=sharing) [[code used]](https://github.com/lisa-analyzer/lisa-tutorial/releases/tag/pldi24)

- Lipari Summer School '24 [[slides]](https://docs.google.com/presentation/d/16MYOHTZJuuzuym9tcIH4L2r24Kn11vjAq7vpyTGcv14/edit?usp=sharing) [[code used]](https://github.com/lisa-analyzer/lisa-tutorial/releases/tag/lipari24)

- Ca' Foscari PhD Course - [[code used]](https://github.com/lisa-analyzer/lisa-tutorial/releases/tag/ssv24)

- Seminar at University of Verona - [[code used]](https://github.com/lisa-analyzer/lisa-tutorial/releases/tag/univr25)

## Implemented classes

### `CongruenceDomain`
Represents the congruence domain defined in the notes, which denotes
numbers of the form `aZ + b`, where `a` and `b` are non-negative integers.
Notably this allows us to represent constants with `0Z + b`. The test
outputs expected results.

### `EqualityDomain`
Represents the relational domain of equal variables. It is a set of
sets of equal variables, for example the knowledge that `x1 = x2 = x3`
and `x4 = x5 = x6` is represented as `{{x1, x2, x3}, {x4, x5, x6}}`. The
test outputs expected results.

### `CongruenceEqualityCartesian`
Represents the cartesian product of the congruence domain and the
equality domain. It is implemented as a trivial cartesian product of the
two domains. The test outputs expected results.
