blaze
----------
A reimplementation of STOKE in haskell.

STOKE is a superoptimizer that finds optimal instruction sequences
to perform a particular task by using MCMC methods to explore the large
search space.


##### High level algorithm

What we do is to "MCMC-sample the space of possible programs, with a
scoring function based on program equivalence and performance". Broken
down, the steps are:

- Start with the original program `p`
- Perturb it slightly to get a program `q` (add an instruction, remove some instructions, change an instruction)
- Assign a score to `q` by sending `p` and `q` random inputs, and checking
  how often they answer the same.
- If they answered the same for _all_ random inputs, ask an SMT solver
  nicely if `p` and `q` are _equivalent_. If she's in a good mood and the
  universe is kind, the answer is yes.
- Now, score `q` based on the factors of:
    1. Are `p` and `q` semantically equivalent?
    2. On how many inputs `p` and `q` had the same answer?
    3. is `q` faster than `p`?
- Now, either pick `q` to be the new `p` or stay at `p` depending on `q`'s
  score.
- Repeat ~10,000 times.
- Order best `q`s visited.


The results are quite impressive: Even with code as naive as what I've written,
we are able to regain peephole optimisations that compilers perform essentially
"for free".

##### Sample output

```
*** original: (nparams: 0 | [IPush 2,IPush 3,IAdd])***
[IPush 5] | score: 2.5 // constant folding
[IPush 2,IPush 3,IAdd] | score: 2.125
[IPush 2,IPush 3,ISwap,IAdd] | score: 2.0625

*** original: (nparams: 1 | [IPush 2,IMul])***
[IDup,IAdd] | score: 2.25 // strength reduction: 2 * x -> x + x
[IDup,ISwap,IAdd] | score: 2.125
[IDup,ISwap,ISwap,IAdd] | score: 2.0625
[IDup,ISwap,ISwap,ISwap,IAdd] | score: 2.03125

*** original: (nparams: 1 | progInsts = [IDup,IAnd])***
[] | score: 3.0 // constant folding: x & x == x
[IDup,IAnd] | score: 2.25
[IDup,ISwap,IAnd] | score: 2.125
```
