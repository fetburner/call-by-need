# call-by-need
This repository contains a formalization of Ariola and Felleisen's call-by-need lambda calculus and a proof of its correpondence with call-by-name. The proof is based on the standardization theorem and the elimination of evaluation contexts. For more detail, see the preprint located in `flops/`.

# Requirements
- Coq 8.5
- Autosubst (https://github.com/uds-psl/autosubst)

# Updates
- Add a formalization of Ariola and Felleisen's original (evaluation context based) calculus on December 29, 2017. Now, we verified the correpondence with call-by-name not only of our modified call-by-need lambda calculus but also of Ariola and Felleisen's original call-by-need lambda calculus.
