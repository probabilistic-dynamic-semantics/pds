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
