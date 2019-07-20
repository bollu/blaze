blaze
----------
A reimplementation of STOKE in haskell.

STOKE is a superoptimizer that finds optimal instruction sequences
to perform a particular task by using MCMC methods to explore the large
search space.

Surprisingly, even a really naive implementation of this seems to do okay.


For example, here is a list of input and output expressions, with `p-x`
and `p-y` being parameters.

```
----
program: (* 2 3)
6 // constant folding
  cost: 0.0
(+ -116 122)
  cost: 1.0
(+ -43 49)
  cost: 1.0
----
program: (* 2 p-x)
(+ p-x p-x) // strength reduction
  cost: 1.0
(* 2 p-x)
  cost: 4.0
----
program: (< (* p-x 1) (* p-y 1))
(< p-x p-y) // constant folding
  cost: 1.0
(< (* p-x 1) (* p-y 1))
  cost: 9.0
```

The problem with using expressions is that it is hard to represent illegal
expressions, and thus it is hard to "gradually" explore the search space.

