# Notes

## Case study

- The shift/one version is broken, contexts are not monotonic

- The proof with DB should go thru even for the **affine** case, as in the var case of sub red the `harmless` assumption is not used

- The typing rule for unit was wrong: it's supposed to be multiplicative (it's observable)
so Delta must be harmeless

- it does not really exercise the algebra much (only commuativity is used and just for convenience)

## Infrastructure 
- what's wrong with having a function for update and some of its special cases such as lookp?