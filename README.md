# call-by-need
This repository contains a formalization of Ariola and Felleisen's call-by-need lambda calculus and a proof of its correpondence with call-by-name. The proof is based on the standardization theorem and the elimination of evaluation contexts. For more detail, see the submission located in `flops/`.

## Directory structure
```
.
├── flops                       # A submission for FLOPS 2018
├── lambda                      # Coq scripts for basic properties of untyped lambda calculus
├── let                         # Coq scripts for Ariola and Felleisen's call-by-need lambda calculus
|   ├── NeedNameCorrespond.v    # A proof of our main theorem, the correspondence between our modified call-by-need lambda calculus and call-by-name lambda calculus
|   └── ContextCorrespond.v     # The correspondence between Ariola and Felleisen's original lambda calculus and call-by-name lambda calculus
├── tpp                         # A slide for TPP 2017
├── .gitignore
├── ARS.v                       # A Coq script for the abstract reduction system
├── README.md
└── _CoqProject
```

## Requirements
- Coq 8.5
- Autosubst (https://github.com/uds-psl/autosubst)

## Updates
- Add a formalization of Ariola and Felleisen's original (evaluation context based) calculus on December 29, 2017. Now, we verified the correpondence with call-by-name, not only of our modified call-by-need lambda calculus, but also of Ariola and Felleisen's original call-by-need lambda calculus.
