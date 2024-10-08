# Formalization of Normalization by Evaluation of System T

This repo formalizes the normalization of evaluation of System T (STLC + Nat + Recursion) in Coq, including totality, soundness and completeness. The proof follows "Normalization by Evaluation: Dependent Typs and Impredicativity". The machanization is based on those in https://github.com/HuStmpHrrr/mech-type-theories which were written in Agda (they are also included in the `./reference` dir).

## Usage 

```
make -f CoqMakefile
```

The proof of System T is in `./systemt/`. 

`./ptt/` contains unfinished work for a extending System T to a dependently typed system. Since its formalization requires induction-recursion which is not currently supported by Coq, it may remain unfinished for a long time (there is a workaround to rely on the impredicativity of `Prop` in Coq, as shown in A "Coq Formalization of Normalization by Evaluation for Martin-Löf Type Theory")

