# Stock map

The source definitions are in
`theories/goodman/Bacon_PP_Question.thy` and
`theories/goodman/notes/Bacon_PP_QSS_Recombination_Bridge.thy`.

| CEV+ component | TFF representation |
|---|---|
| `pp_purity_schema` | Selected closed logical purity instances in `00_common_semantics.tff.in` |
| `pp_application_closure_schema` | `pure_application_prop`, `pure_application_unary`, `pure_composition`, `pure_pointwise_eq`, and `pure_mf_prop` |
| `pp_unique_fundamental Prop` | `unique_proposition_fundamental` |
| `pp_no_other_fundamentals_schema` | `no_unary_operator_fundamentals` and `no_classifier_fundamentals` |
| `pp_zeroary_recombination` | `zeroary_recombination` |
| `pp_unary_recombination` | `unary_recombination` |
| `pp_zeroary_exhaustion` | `zeroary_exhaustion` |
| `pp_unary_exhaustion` | `unary_exhaustion` |
| `pp_target_PP` | `goodman_PP_at_unary_classifier_type` |
| Proposition identity | `eq_prop_at`, with rigidity represented by `proposition_identity_is_necessary` |
| Unary-operator identity | `eq_op_at`, with `modalized_functionality` as the required bridge |
| `pp_fun_prime` | `fun_prime_definition`, using `eq_prop_at` and `eq_op_at` |
| `pp_L2` | `weak_L2_definition`, used only as a conjectural target |

The representation of PP is type-sensitive:

```text
pure_prop_classifier  : op1
pure_unary_classifier : op2
PP                     : pure_op2_at(W,pure_unary_classifier)
```

Thus PP is not conflated with
`pure_op_at(W,pure_prop_classifier)`, the logical-purity instance saying that
`Pure_Prop` is pure.

No file in this suite declares the T6 diagonal, Purity of Fun, TU, WI, Inv,
RS, strong L2, or the denial of L2.
