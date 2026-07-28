theory Bacon_PP_ZF_Goodman_L2_Global_Reduction
  imports Bacon_PP_ZF_Goodman_L2_Model
begin

section \<open>Global semantic L2: the remaining classification problem\<close>

text \<open>
  We continue to use exactly Bacon's stock of unary operators denoted by
  closed terms containing only logical vocabulary.  The following relation
  records when two such operators induce the same agreements after a further
  pure operator is applied.  It is stated entirely in terms of composition
  inside the closed logical stock.
\<close>

definition pp_b_exact_same_composition_agreements ::
    "pp_b_operator \<Rightarrow> pp_b_operator \<Rightarrow> bool" where
  "pp_b_exact_same_composition_agreements X Y \<longleftrightarrow>
    (\<forall>A \<in> pp_b_exact_stock.
      \<forall>B \<in> pp_b_exact_stock.
        (A \<circ> X = B \<circ> X \<longleftrightarrow>
         A \<circ> Y = B \<circ> Y))"

theorem pp_b_exact_fun_prime_collision_composition_agreements:
  assumes X: "X \<in> pp_b_exact_stock"
    and Y: "Y \<in> pp_b_exact_stock"
    and p: "pp_b_exact_fun_prime p"
    and q: "pp_b_exact_fun_prime q"
    and collision: "X p = Y q"
  shows "pp_b_exact_same_composition_agreements X Y"
proof (unfold pp_b_exact_same_composition_agreements_def,
    intro ballI iffI)
  fix A B
  assume A: "A \<in> pp_b_exact_stock"
    and B: "B \<in> pp_b_exact_stock"
    and AX_BX: "A \<circ> X = B \<circ> X"
  have AX: "A \<circ> X \<in> pp_b_exact_stock"
    using A X by (rule pp_b_exact_stock_compose)
  have BX: "B \<circ> X \<in> pp_b_exact_stock"
    using B X by (rule pp_b_exact_stock_compose)
  have AY: "A \<circ> Y \<in> pp_b_exact_stock"
    using A Y by (rule pp_b_exact_stock_compose)
  have BY: "B \<circ> Y \<in> pp_b_exact_stock"
    using B Y by (rule pp_b_exact_stock_compose)
  have at_Xp: "A (X p) = B (X p)"
    using fun_cong[OF AX_BX, of p] by simp
  have at_Yq: "A (Y q) = B (Y q)"
    using at_Xp collision by simp
  have at_q: "(A \<circ> Y) q = (B \<circ> Y) q"
    using at_Yq by simp
  show "A \<circ> Y = B \<circ> Y"
    using q AY BY at_q by (rule pp_b_exact_fun_primeD)
next
  fix A B
  assume A: "A \<in> pp_b_exact_stock"
    and B: "B \<in> pp_b_exact_stock"
    and AY_BY: "A \<circ> Y = B \<circ> Y"
  have AX: "A \<circ> X \<in> pp_b_exact_stock"
    using A X by (rule pp_b_exact_stock_compose)
  have BX: "B \<circ> X \<in> pp_b_exact_stock"
    using B X by (rule pp_b_exact_stock_compose)
  have AY: "A \<circ> Y \<in> pp_b_exact_stock"
    using A Y by (rule pp_b_exact_stock_compose)
  have BY: "B \<circ> Y \<in> pp_b_exact_stock"
    using B Y by (rule pp_b_exact_stock_compose)
  have at_Yq: "A (Y q) = B (Y q)"
    using fun_cong[OF AY_BY, of q] by simp
  have at_Xp: "A (X p) = B (X p)"
    using at_Yq collision by simp
  have at_p: "(A \<circ> X) p = (B \<circ> X) p"
    using at_Xp by simp
  show "A \<circ> X = B \<circ> X"
    using p AX BX at_p by (rule pp_b_exact_fun_primeD)
qed

text \<open>
  Thus the global L2 question is reduced to a precise classification claim:
  if two closed logical operators induce the same composition agreements,
  they are of the same kind.  No assumption about propositions outside
  Bacon's model is used in this reduction.
\<close>

definition pp_b_exact_composition_classification :: bool where
  "pp_b_exact_composition_classification \<longleftrightarrow>
    (\<forall>X \<in> pp_b_exact_stock.
      \<forall>Y \<in> pp_b_exact_stock.
        pp_b_exact_same_composition_agreements X Y \<longrightarrow>
        pp_b_exact_same_kind X Y)"

theorem pp_b_exact_L2_from_composition_classification:
  assumes classification: "pp_b_exact_composition_classification"
  shows "pp_b_exact_L2"
proof (unfold pp_b_exact_L2_def, intro ballI)
  fix X Y
  assume X: "X \<in> pp_b_exact_stock"
    and Y: "Y \<in> pp_b_exact_stock"
  show "pp_b_exact_L2_pair X Y"
  proof (unfold pp_b_exact_L2_pair_def, intro conjI)
    show "X \<in> pp_b_exact_stock"
      by (rule X)
    show "Y \<in> pp_b_exact_stock"
      by (rule Y)
    show "\<forall>p q.
        pp_b_exact_fun_prime p \<longrightarrow>
        pp_b_exact_fun_prime q \<longrightarrow>
        X p = Y q \<longrightarrow>
        pp_b_exact_same_kind X Y"
    proof (intro allI impI)
      fix p q
      assume p: "pp_b_exact_fun_prime p"
        and q: "pp_b_exact_fun_prime q"
        and collision: "X p = Y q"
      have agreements:
          "pp_b_exact_same_composition_agreements X Y"
        using X Y p q collision
        by (rule pp_b_exact_fun_prime_collision_composition_agreements)
      show "pp_b_exact_same_kind X Y"
        using classification X Y agreements
        unfolding pp_b_exact_composition_classification_def by blast
    qed
  qed
qed

subsection \<open>When an operator carries fun-prime to fun-prime\<close>

definition pp_b_exact_right_cancellative ::
    "pp_b_operator \<Rightarrow> bool" where
  "pp_b_exact_right_cancellative X \<longleftrightarrow>
    (\<forall>A \<in> pp_b_exact_stock.
      \<forall>B \<in> pp_b_exact_stock.
        A \<circ> X = B \<circ> X \<longrightarrow> A = B)"

theorem pp_b_exact_fun_prime_image_iff_right_cancellative:
  assumes X: "X \<in> pp_b_exact_stock"
    and p: "pp_b_exact_fun_prime p"
  shows "pp_b_exact_fun_prime (X p) \<longleftrightarrow>
    pp_b_exact_right_cancellative X"
proof
  assume image: "pp_b_exact_fun_prime (X p)"
  show "pp_b_exact_right_cancellative X"
  proof (unfold pp_b_exact_right_cancellative_def, intro ballI impI)
    fix A B
    assume A: "A \<in> pp_b_exact_stock"
      and B: "B \<in> pp_b_exact_stock"
      and equality: "A \<circ> X = B \<circ> X"
    have at_image: "A (X p) = B (X p)"
      using fun_cong[OF equality, of p] by simp
    show "A = B"
      using image A B at_image by (rule pp_b_exact_fun_primeD)
  qed
next
  assume cancellation: "pp_b_exact_right_cancellative X"
  show "pp_b_exact_fun_prime (X p)"
  proof (rule pp_b_exact_fun_primeI)
    fix A B
    assume A: "A \<in> pp_b_exact_stock"
      and B: "B \<in> pp_b_exact_stock"
      and at_image: "A (X p) = B (X p)"
    have AX: "A \<circ> X \<in> pp_b_exact_stock"
      using A X by (rule pp_b_exact_stock_compose)
    have BX: "B \<circ> X \<in> pp_b_exact_stock"
      using B X by (rule pp_b_exact_stock_compose)
    have at_p: "(A \<circ> X) p = (B \<circ> X) p"
      using at_image by simp
    have composition: "A \<circ> X = B \<circ> X"
      using p AX BX at_p by (rule pp_b_exact_fun_primeD)
    show "A = B"
      using cancellation A B composition
      unfolding pp_b_exact_right_cancellative_def by blast
  qed
qed

lemma pp_b_exact_same_kind_id_imp_reversible:
  assumes kind: "pp_b_exact_same_kind id Z"
  shows "Z \<in> pp_b_exact_G"
proof -
  obtain W where W: "W \<in> pp_b_exact_G"
    and id_ZW: "id = Z \<circ> W"
    using kind unfolding pp_b_exact_same_kind_def by blast
  obtain V where V_stock: "V \<in> pp_b_exact_stock"
    and WV: "W \<circ> V = id"
    and VW: "V \<circ> W = id"
    using W by (rule pp_b_exact_GE)
  have V_G: "V \<in> pp_b_exact_G"
    using W V_stock WV VW by (rule pp_b_exact_G_inverse)
  have Z_V: "Z = V"
  proof (rule ext)
    fix x
    have wv: "W (V x) = x"
      using fun_cong[OF WV, of x] by simp
    have zw: "Z (W (V x)) = V x"
      using fun_cong[OF id_ZW, of "V x"] by simp
    show "Z x = V x"
      using wv zw by simp
  qed
  show ?thesis
    using V_G Z_V by simp
qed

theorem pp_b_exact_right_cancellative_nonreversible_refutes_L2:
  assumes Z: "Z \<in> pp_b_exact_stock"
    and cancellation: "pp_b_exact_right_cancellative Z"
    and nonreversible: "Z \<notin> pp_b_exact_G"
  shows "\<not> pp_b_exact_L2"
proof -
  obtain p where p: "pp_b_exact_fun_prime p"
    using pp_b_exact_fun_prime_exists by blast
  have Zp: "pp_b_exact_fun_prime (Z p)"
    using pp_b_exact_fun_prime_image_iff_right_cancellative[
      OF Z p] cancellation by blast
  have collision: "id (Z p) = Z p"
    by simp
  have not_kind: "\<not> pp_b_exact_same_kind id Z"
    using nonreversible pp_b_exact_same_kind_id_imp_reversible
    by blast
  have counterexample:
      "pp_b_exact_L2_counterexample id Z (Z p) p"
    unfolding pp_b_exact_L2_counterexample_def
    using pp_b_exact_base_operators(1) Z Zp p collision not_kind
    by blast
  show ?thesis
    using pp_b_exact_not_L2_iff_counterexample counterexample
    by blast
qed

corollary pp_b_exact_L2_requires_right_cancellative_reversible:
  assumes L2: "pp_b_exact_L2"
    and Z: "Z \<in> pp_b_exact_stock"
    and cancellation: "pp_b_exact_right_cancellative Z"
  shows "Z \<in> pp_b_exact_G"
proof (rule ccontr)
  assume "Z \<notin> pp_b_exact_G"
  have "\<not> pp_b_exact_L2"
    using Z cancellation \<open>Z \<notin> pp_b_exact_G\<close>
    by (rule pp_b_exact_right_cancellative_nonreversible_refutes_L2)
  show False
    using L2 \<open>\<not> pp_b_exact_L2\<close> by contradiction
qed

subsection \<open>Concrete tests of the remaining condition\<close>

lemma pp_b_exact_identity_right_cancellative:
  "pp_b_exact_right_cancellative id"
  unfolding pp_b_exact_right_cancellative_def by simp

lemma pp_b_exact_complement_right_cancellative:
  "pp_b_exact_right_cancellative pp_b_complement"
proof (unfold pp_b_exact_right_cancellative_def, intro ballI impI)
  fix A B
  assume equality:
      "A \<circ> pp_b_complement = B \<circ> pp_b_complement"
  show "A = B"
  proof (rule ext)
    fix P
    have at_complement:
        "A (pp_b_complement (pp_b_complement P)) =
         B (pp_b_complement (pp_b_complement P))"
      using fun_cong[OF equality, of "pp_b_complement P"]
      by simp
    show "A P = B P"
      using at_complement
      by (simp add: pp_b_complement_def)
  qed
qed

lemma pp_b_exact_complement_reversible:
  "pp_b_complement \<in> pp_b_exact_G"
proof -
  have involution:
      "pp_b_complement \<circ> pp_b_complement = id"
    by (rule ext)
      (simp add: pp_b_complement_def)
  show ?thesis
    unfolding pp_b_exact_G_def pp_b_exact_reversible_def
    using pp_b_exact_complement involution by blast
qed

theorem pp_b_exact_box_left_composition_not_right_cancellative:
  assumes H: "H \<in> pp_b_exact_stock"
  shows "\<not> pp_b_exact_right_cancellative (pp_b_box \<circ> H)"
proof
  assume cancellation:
      "pp_b_exact_right_cancellative (pp_b_box \<circ> H)"
  have Z: "pp_b_box \<circ> H \<in> pp_b_exact_stock"
    using pp_b_exact_base_operators(4) H
    by (rule pp_b_exact_stock_compose)
  have equality:
      "id \<circ> (pp_b_box \<circ> H) =
       pp_b_box \<circ> (pp_b_box \<circ> H)"
  proof (rule ext)
    fix P
    show "(id \<circ> (pp_b_box \<circ> H)) P =
        (pp_b_box \<circ> (pp_b_box \<circ> H)) P"
      by (simp add: pp_b_box_idempotent)
  qed
  have "(id :: pp_b_operator) = pp_b_box"
    using cancellation pp_b_exact_base_operators(1,4) equality
    unfolding pp_b_exact_right_cancellative_def by blast
  show False
    using pp_b_id_neq_box \<open>(id :: pp_b_operator) = pp_b_box\<close>
    by contradiction
qed

theorem pp_b_exact_diamond_left_composition_not_right_cancellative:
  assumes H: "H \<in> pp_b_exact_stock"
  shows "\<not> pp_b_exact_right_cancellative
    (pp_b_diamond \<circ> H)"
proof
  assume cancellation:
      "pp_b_exact_right_cancellative (pp_b_diamond \<circ> H)"
  have Z: "pp_b_diamond \<circ> H \<in> pp_b_exact_stock"
    using pp_b_exact_base_operators(5) H
    by (rule pp_b_exact_stock_compose)
  have equality:
      "id \<circ> (pp_b_diamond \<circ> H) =
       pp_b_diamond \<circ> (pp_b_diamond \<circ> H)"
  proof (rule ext)
    fix P
    show "(id \<circ> (pp_b_diamond \<circ> H)) P =
        (pp_b_diamond \<circ> (pp_b_diamond \<circ> H)) P"
      by (simp add: pp_b_diamond_idempotent)
  qed
  have "(id :: pp_b_operator) = pp_b_diamond"
    using cancellation pp_b_exact_base_operators(1,5) equality
    unfolding pp_b_exact_right_cancellative_def by blast
  show False
    using pp_b_id_neq_diamond
      \<open>(id :: pp_b_operator) = pp_b_diamond\<close>
    by contradiction
qed

corollary pp_b_exact_box_not_right_cancellative:
  "\<not> pp_b_exact_right_cancellative pp_b_box"
proof -
  have "\<not> pp_b_exact_right_cancellative (pp_b_box \<circ> id)"
    using pp_b_exact_base_operators(1)
    by (rule pp_b_exact_box_left_composition_not_right_cancellative)
  then show ?thesis
    by simp
qed

corollary pp_b_exact_diamond_not_right_cancellative:
  "\<not> pp_b_exact_right_cancellative pp_b_diamond"
proof -
  have "\<not> pp_b_exact_right_cancellative
      (pp_b_diamond \<circ> id)"
    using pp_b_exact_base_operators(1)
    by (rule pp_b_exact_diamond_left_composition_not_right_cancellative)
  then show ?thesis
    by simp
qed

corollary pp_b_exact_diamond_box_not_right_cancellative:
  "\<not> pp_b_exact_right_cancellative pp_b_diamond_box"
proof -
  have "\<not> pp_b_exact_right_cancellative
      (pp_b_diamond \<circ> pp_b_box)"
    using pp_b_exact_base_operators(4)
    by (rule pp_b_exact_diamond_left_composition_not_right_cancellative)
  moreover have
      "pp_b_diamond_box = pp_b_diamond \<circ> pp_b_box"
    by (rule ext)
      (simp add: pp_b_diamond_box_def)
  ultimately show ?thesis by simp
qed

corollary pp_b_exact_possible_impossible_not_right_cancellative:
  "\<not> pp_b_exact_right_cancellative pp_b_possible_impossible"
proof -
  have H: "pp_b_box \<circ> pp_b_complement \<in> pp_b_exact_stock"
    using pp_b_exact_base_operators(4) pp_b_exact_complement
    by (rule pp_b_exact_stock_compose)
  have "\<not> pp_b_exact_right_cancellative
      (pp_b_diamond \<circ> (pp_b_box \<circ> pp_b_complement))"
    using H
    by (rule pp_b_exact_diamond_left_composition_not_right_cancellative)
  moreover have "pp_b_possible_impossible =
      pp_b_diamond \<circ> (pp_b_box \<circ> pp_b_complement)"
    by (rule ext)
      (simp add: pp_b_possible_impossible_def
        pp_b_complement_def)
  ultimately show ?thesis by simp
qed

subsection \<open>Cases already settled for the complete stock\<close>

lemma pp_b_exact_L2_pair_if_same_kind:
  assumes X: "X \<in> pp_b_exact_stock"
    and Y: "Y \<in> pp_b_exact_stock"
    and kind: "pp_b_exact_same_kind X Y"
  shows "pp_b_exact_L2_pair X Y"
  using assms unfolding pp_b_exact_L2_pair_def by blast

theorem pp_b_exact_L2_const_true_left:
  assumes Y: "Y \<in> pp_b_exact_stock"
  shows "pp_b_exact_L2_pair pp_b_const_true Y"
proof (unfold pp_b_exact_L2_pair_def, intro conjI)
  show "pp_b_const_true \<in> pp_b_exact_stock"
    by (rule pp_b_exact_base_operators(2))
  show "Y \<in> pp_b_exact_stock"
    by (rule Y)
  show "\<forall>p q.
      pp_b_exact_fun_prime p \<longrightarrow>
      pp_b_exact_fun_prime q \<longrightarrow>
      pp_b_const_true p = Y q \<longrightarrow>
      pp_b_exact_same_kind pp_b_const_true Y"
  proof (intro allI impI)
    fix p q
    assume q: "pp_b_exact_fun_prime q"
      and collision: "pp_b_const_true p = Y q"
    have agreement: "pp_b_const_true q = Y q"
      using collision by (simp add: pp_b_const_true_def)
    have equality: "pp_b_const_true = Y"
      using q pp_b_exact_base_operators(2) Y agreement
      by (rule pp_b_exact_fun_primeD)
    show "pp_b_exact_same_kind pp_b_const_true Y"
      using equality pp_b_exact_same_kind_refl by simp
  qed
qed

theorem pp_b_exact_L2_const_false_left:
  assumes Y: "Y \<in> pp_b_exact_stock"
  shows "pp_b_exact_L2_pair pp_b_const_false Y"
proof (unfold pp_b_exact_L2_pair_def, intro conjI)
  show "pp_b_const_false \<in> pp_b_exact_stock"
    by (rule pp_b_exact_base_operators(3))
  show "Y \<in> pp_b_exact_stock"
    by (rule Y)
  show "\<forall>p q.
      pp_b_exact_fun_prime p \<longrightarrow>
      pp_b_exact_fun_prime q \<longrightarrow>
      pp_b_const_false p = Y q \<longrightarrow>
      pp_b_exact_same_kind pp_b_const_false Y"
  proof (intro allI impI)
    fix p q
    assume q: "pp_b_exact_fun_prime q"
      and collision: "pp_b_const_false p = Y q"
    have agreement: "pp_b_const_false q = Y q"
      using collision by (simp add: pp_b_const_false_def)
    have equality: "pp_b_const_false = Y"
      using q pp_b_exact_base_operators(3) Y agreement
      by (rule pp_b_exact_fun_primeD)
    show "pp_b_exact_same_kind pp_b_const_false Y"
      using equality pp_b_exact_same_kind_refl by simp
  qed
qed

lemma pp_b_exact_L2_pair_sym:
  assumes pair: "pp_b_exact_L2_pair X Y"
  shows "pp_b_exact_L2_pair Y X"
proof -
  have X: "X \<in> pp_b_exact_stock"
    and Y: "Y \<in> pp_b_exact_stock"
    using pair unfolding pp_b_exact_L2_pair_def by blast+
  show ?thesis
  proof (unfold pp_b_exact_L2_pair_def, intro conjI)
    show "Y \<in> pp_b_exact_stock"
      by (rule Y)
    show "X \<in> pp_b_exact_stock"
      by (rule X)
    show "\<forall>p q.
        pp_b_exact_fun_prime p \<longrightarrow>
        pp_b_exact_fun_prime q \<longrightarrow>
        Y p = X q \<longrightarrow>
        pp_b_exact_same_kind Y X"
    proof (intro allI impI)
      fix p q
      assume p: "pp_b_exact_fun_prime p"
        and q: "pp_b_exact_fun_prime q"
        and collision: "Y p = X q"
      have XY: "pp_b_exact_same_kind X Y"
        using pair q p collision
        unfolding pp_b_exact_L2_pair_def by blast
      show "pp_b_exact_same_kind Y X"
        using XY by (rule pp_b_exact_same_kind_sym)
    qed
  qed
qed

corollary pp_b_exact_L2_const_true_right:
  assumes X: "X \<in> pp_b_exact_stock"
  shows "pp_b_exact_L2_pair X pp_b_const_true"
  using pp_b_exact_L2_const_true_left[OF X]
  by (rule pp_b_exact_L2_pair_sym)

corollary pp_b_exact_L2_const_false_right:
  assumes X: "X \<in> pp_b_exact_stock"
  shows "pp_b_exact_L2_pair X pp_b_const_false"
  using pp_b_exact_L2_const_false_left[OF X]
  by (rule pp_b_exact_L2_pair_sym)

lemma pp_b_exact_G_same_kind:
  assumes X: "X \<in> pp_b_exact_G"
    and Y: "Y \<in> pp_b_exact_G"
  shows "pp_b_exact_same_kind X Y"
proof -
  have X_id: "pp_b_exact_same_kind X id"
    unfolding pp_b_exact_same_kind_def
    using X by auto
  have Y_id: "pp_b_exact_same_kind Y id"
    unfolding pp_b_exact_same_kind_def
    using Y by auto
  have id_Y: "pp_b_exact_same_kind id Y"
    using Y_id by (rule pp_b_exact_same_kind_sym)
  show ?thesis
    using X_id id_Y by (rule pp_b_exact_same_kind_trans)
qed

theorem pp_b_exact_L2_on_reversibles:
  assumes X: "X \<in> pp_b_exact_G"
    and Y: "Y \<in> pp_b_exact_G"
  shows "pp_b_exact_L2_pair X Y"
proof -
  have X_stock: "X \<in> pp_b_exact_stock"
    using X by (rule pp_b_exact_GE)
  have Y_stock: "Y \<in> pp_b_exact_stock"
    using Y by (rule pp_b_exact_GE)
  have kind: "pp_b_exact_same_kind X Y"
    using X Y by (rule pp_b_exact_G_same_kind)
  show ?thesis
    using X_stock Y_stock kind
    by (rule pp_b_exact_L2_pair_if_same_kind)
qed

text \<open>
  These results settle L2 for every pair already of the same kind, for every
  pair of reversible closed logical operators, and for every pair in which
  one operator is constant truth or constant falsity.  The unresolved case
  consists of distinct kinds represented by nonconstant, nonreversible
  operators.  A proof of the composition classification above would close
  that case and hence establish global semantic L2 for Bacon's complete
  definable stock.  Conversely, a nonreversible closed logical operator
  whose composition on the right preserves distinctness would give an
  explicit counterexample to global L2 by the theorem above.  Necessity,
  possibility, every operator beginning with either of them, the composition
  possibility-after-necessity, and the displayed possibly-impossible
  operator have now been excluded from that negative route.  Identity and
  negation preserve distinctness, but both are reversible.
\<close>

end
