# Probabilistic dynamic semantics

Develop probabilistic semantic grammar fragments and convert them to Stan code.

## Overview

Semantic research in the Montagovian tradition has taken an experimental turn in the last decade, as the empirical goals of semanticists have gotten ever loftier.
Large-scale inference datasets---and the statistical models they require---have become a more standard part of the semanticist's toolkit.
`pds` is an approach to developing models of inference datasets that involves seamlessly deriving them from semantic grammar fragments.
As a library, it encodes the ideas described in [Probabilistic Dynamic Semantics](https://lingbuzz.net/lingbuzz/008478) by [Julian Grove](https://juliangrove.github.io/) and [Aaron Steven White](https://aaronstevenwhite.io/).
Applications of the framework can also be found in [Grove and White (2025a)](https://ling.auf.net/lingbuzz/007450) [Grove and White (2025b)](https://journals.linguisticsociety.org/proceedings/index.php/ELM/article/view/5857).

### Features

- [`Framework`](https://github.com/probabilistic-dynamic-semantics/pds/tree/main/src/Framework):
  - An encoding of Combinatory Categorial Grammar (CCG)-based grammar fragments, as well as a CKY-style parser with string-based (instead of span-based) memoization.
  - A framework for typed λ-calculus based on δ-rules, which transform complex semantic representations into simpler probabilistic models.
  - Code for transforming typed λ-terms into models in the [Stan](https://mc-stan.org/) programming language.
- [`Theory`](https://github.com/probabilistic-dynamic-semantics/pds/tree/main/src/Theory):
  - An encoding of theories of formal pragmatics, including common grounds and Questions Under Discussion (QUDs).
- [`Analysis`](https://github.com/probabilistic-dynamic-semantics/pds/tree/main/src/Analysis):
  - Analyses of particular natural language phenomena, including factivity and vagueness.

## Documentation

See both the text [Probabilistic Dynamic Semantics](https://lingbuzz.net/lingbuzz/008478), as well as the ESSLI 2025 Summer School [Course Notes](https://juliangrove.github.io/esslli-2025/notes/).

## Installation

You can install the library and open a repl by cloning this repository doing:

```
cd pds
cabal v2-repl --repl-options="-ghci-script .ghci"
```

A [`Nix`](https://nixos.org/)-based installation is also possible, by doing:

```
cd pds
nix-shell --run "cabal v2-repl --repl-options=\"-ghci-script .ghci\""
```

## Quick start

There is a test-suite under active development in [here](https://github.com/probabilistic-dynamic-semantics/pds/blob/readme/test/Spec.hs).
To load the examples which are currently implemented in [`Analysis`], install the library and load the test-suite:

```
ghci> :l test/Spec.hs
```

There are three models in the test-suite which can be printed out.
The model on factivity can be gotten by doing:

```
stanOutput factivityExample
```

It yields the following result:

```
model {
  // FIXED EFFECTS
  v ~ logit_normal(0.0, 1.0);
  w ~ logit_normal(0.0, 1.0);

  // LIKELIHOOD
  target += log_mix(v, truncated_normal_lpdf(y | 1.0, sigma, 0.0, 1.0), truncated_normal_lpdf(y | w, sigma, 0.0, 1.0));
}
```

The other two models are `scaleNormingExample` and `likelihoodExample`.
