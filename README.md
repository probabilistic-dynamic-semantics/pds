# pds

Develop probabilistic semantic grammar fragments and convert them to Stan code.

`cabal v2-repl --repl-options="-ghci-script .ghci"`

```
ghci> stanOutput simplified
model {
  // FIXED EFFECTS
  v ~ logit_normal(0.0, 1.0);
  w ~ logit_normal(0.0, 1.0);

  // LIKELIHOOD
  target += log_mix(v, truncated_normal_lpdf(y | 1.0, sigma, 0.0, 1.0), truncated_normal_lpdf(y | w, sigma, 0.0, 1.0));
}
```
