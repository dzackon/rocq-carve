# This autosubst dir

We're trying to make Carve and Autosubst (the ocaml version) work together. 

The case study is the simply typed lambda calculus, with progress and preservation, which we will interpret (sub)structurally in the various subdir. So we have already code generated the syntax (`stlc.v`). At the top level we have the basic defs common to any Autosubst development (ARS, core, fintype, etc). Since the operational semantics is the same, you'll find it at the same level: `step.v`

## Chapter 9
Taken more or less directly from Kath's thesis, this is the **intutionistic** case, done in the _well-scoped_ style. It comes in two versions

- `presFun.v`, where the context is a total function `fin n -> ty`. Preservation is literally the same as the one in Kath's thesis.
- `preservation.v`, where the context is a length indexed vector of types

``` coq
Definition ctx n := vlist ty n.
```
Progress is adapted from SF.

In the vector case, proofs are a tad more complex because of dependencies and lookups over vectors.

## substruct

**Now commented out for make reasons**

This is the *well_scoped* porting of Chapter 9 in the sub-structural
sense. Again it should comes in the two above versions and it's work
in progress (to be optimistic).  Let's concentrata on the ctx as function one.
Since we  prove progress, we need an empty ctx. 

 - ftps0: we follow Kath and take the empty ctx as one with domain
	 `fin 0` (viz `null` in fintype): this brings some complications
	 (dependent induction, JMeq).  It does work
	 and in fact it is used in Chapter9 as well. This is the version I'm worlking on.

- ftps: another way is to identify empty with an infinite ctx with
	everything is zero. This may work, but we'll see.
	

- tps: this is list based -- please ignore for the time being since it is not clear if it should be done with vectors that CARVe does not support yet and may never will. In fact, it's "commented out"





Open issues:

- algebraic thms to prove: 
`Lemma emptyT_is_id: identity null`. 

- define updn so that the var rule makes sense

- prove that the generalization of  ltc  is preserved under join

  -  the multiplicity changes but the type is the same
  -  careful about the indexes of the renamings

