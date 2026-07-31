theory Bacon_PP_ZF_Goodman_L2_Stock_Expansion
  imports Bacon_PP_ZF_Goodman_L2_Child_Xor
begin

section \<open>L2 under enlargement of the pure stock\<close>

text \<open>
  The counterexample supplied by the immediate-successor operator does not
  depend on taking the pure unary operators to be exactly the denotations of
  closed logical terms.  We formulate L2 relative to an arbitrary unary
  stock.  If the stock contains the closed logical operators, is closed under
  composition, and has a \<open>fun\<acute>\<close> proposition, then the same operator refutes
  L2.  Thus enlarging the stock by adding the interpretation of \<open>Pure\<close>
  cannot by itself restore L2 on Bacon's tree frame.
\<close>

definition pp_b_stock_fun_prime ::
    "pp_b_operator set \<Rightarrow> pp_b_prop \<Rightarrow> bool" where
  "pp_b_stock_fun_prime S p \<longleftrightarrow>
    (\<forall>X \<in> S. \<forall>Y \<in> S. X p = Y p \<longrightarrow> X = Y)"

definition pp_b_stock_reversible ::
    "pp_b_operator set \<Rightarrow> pp_b_operator \<Rightarrow> bool" where
  "pp_b_stock_reversible S Z \<longleftrightarrow>
    Z \<in> S \<and>
    (\<exists>W \<in> S. Z \<circ> W = id \<and> W \<circ> Z = id)"

definition pp_b_stock_group ::
    "pp_b_operator set \<Rightarrow> pp_b_operator set" where
  "pp_b_stock_group S = {Z. pp_b_stock_reversible S Z}"

definition pp_b_stock_same_kind ::
    "pp_b_operator set \<Rightarrow>
      pp_b_operator \<Rightarrow> pp_b_operator \<Rightarrow> bool" where
  "pp_b_stock_same_kind S X Y \<longleftrightarrow>
    (\<exists>Z \<in> pp_b_stock_group S. X = Y \<circ> Z)"

definition pp_b_stock_L2 ::
    "pp_b_operator set \<Rightarrow> bool" where
  "pp_b_stock_L2 S \<longleftrightarrow>
    (\<forall>X \<in> S. \<forall>Y \<in> S. \<forall>p q.
      pp_b_stock_fun_prime S p \<longrightarrow>
      pp_b_stock_fun_prime S q \<longrightarrow>
      X p = Y q \<longrightarrow>
      pp_b_stock_same_kind S X Y)"

lemma pp_b_stock_fun_primeI:
  assumes "\<And>X Y. X \<in> S \<Longrightarrow> Y \<in> S \<Longrightarrow>
    X p = Y p \<Longrightarrow> X = Y"
  shows "pp_b_stock_fun_prime S p"
  using assms unfolding pp_b_stock_fun_prime_def by blast

lemma pp_b_stock_fun_primeD:
  assumes "pp_b_stock_fun_prime S p"
    and "X \<in> S" and "Y \<in> S" and "X p = Y p"
  shows "X = Y"
  using assms unfolding pp_b_stock_fun_prime_def by blast

lemma pp_b_surjective_right_cancellation:
  assumes surjective: "surj Z"
    and equality: "A \<circ> Z = B \<circ> Z"
  shows "A = B"
proof (rule ext)
  fix q
  obtain p where "q = Z p"
    using surjective unfolding surj_def by blast
  have "A (Z p) = B (Z p)"
    using fun_cong[OF equality, of p] by simp
  then show "A q = B q"
    using \<open>q = Z p\<close> by simp
qed

lemma pp_b_stock_fun_prime_surjective_image:
  assumes Z: "Z \<in> S"
    and closed:
      "\<And>A B. A \<in> S \<Longrightarrow> B \<in> S \<Longrightarrow> A \<circ> B \<in> S"
    and p: "pp_b_stock_fun_prime S p"
    and surjective: "surj Z"
  shows "pp_b_stock_fun_prime S (Z p)"
proof (rule pp_b_stock_fun_primeI)
  fix A B
  assume A: "A \<in> S"
    and B: "B \<in> S"
    and at_image: "A (Z p) = B (Z p)"
  have AZ: "A \<circ> Z \<in> S"
    using A Z by (rule closed)
  have BZ: "B \<circ> Z \<in> S"
    using B Z by (rule closed)
  have at_p: "(A \<circ> Z) p = (B \<circ> Z) p"
    using at_image by simp
  have composition: "A \<circ> Z = B \<circ> Z"
    using p AZ BZ at_p by (rule pp_b_stock_fun_primeD)
  show "A = B"
    using surjective composition
    by (rule pp_b_surjective_right_cancellation)
qed

lemma pp_b_stock_same_kind_identity_implies_injective:
  assumes kind: "pp_b_stock_same_kind S id Z"
  shows "inj Z"
proof -
  obtain G where G_group: "G \<in> pp_b_stock_group S"
    and identity: "id = Z \<circ> G"
    using kind unfolding pp_b_stock_same_kind_def by blast
  obtain W where GW: "G \<circ> W = id"
    and WG: "W \<circ> G = id"
    using G_group
    unfolding pp_b_stock_group_def pp_b_stock_reversible_def
    by blast
  have ZW: "Z = W"
  proof (rule ext)
    fix p
    have G_Wp: "G (W p) = p"
      using fun_cong[OF GW, of p] by simp
    have Z_GWp: "Z (G (W p)) = W p"
      using fun_cong[OF identity, of "W p"] by simp
    show "Z p = W p"
      using G_Wp Z_GWp by simp
  qed
  have left_inverse: "G \<circ> Z = id"
    using GW ZW by simp
  show "inj Z"
  proof (rule injI)
    fix p q
    assume "Z p = Z q"
    then have "G (Z p) = G (Z q)"
      by simp
    then show "p = q"
      using fun_cong[OF left_inverse, of p]
        fun_cong[OF left_inverse, of q]
      by simp
  qed
qed

theorem pp_b_surjective_noninjective_refutes_stock_L2:
  assumes identity: "id \<in> S"
    and Z: "Z \<in> S"
    and closed:
      "\<And>A B. A \<in> S \<Longrightarrow> B \<in> S \<Longrightarrow> A \<circ> B \<in> S"
    and witness: "\<exists>p. pp_b_stock_fun_prime S p"
    and surjective: "surj Z"
    and noninjective: "\<not> inj Z"
  shows "\<not> pp_b_stock_L2 S"
proof
  assume L2: "pp_b_stock_L2 S"
  obtain p where p: "pp_b_stock_fun_prime S p"
    using witness by blast
  have Zp: "pp_b_stock_fun_prime S (Z p)"
    using Z closed p surjective
    by (rule pp_b_stock_fun_prime_surjective_image)
  have same_kind: "pp_b_stock_same_kind S id Z"
    using L2 identity Z Zp p
    unfolding pp_b_stock_L2_def by simp
  have "inj Z"
    using same_kind
    by (rule pp_b_stock_same_kind_identity_implies_injective)
  show False
    using noninjective \<open>inj Z\<close> by contradiction
qed

theorem pp_b_child_xor_refutes_L2_in_every_closed_expansion:
  assumes expansion: "pp_b_exact_stock \<subseteq> S"
    and closed:
      "\<And>A B. A \<in> S \<Longrightarrow> B \<in> S \<Longrightarrow> A \<circ> B \<in> S"
    and witness: "\<exists>p. pp_b_stock_fun_prime S p"
  shows "\<not> pp_b_stock_L2 S"
proof -
  have identity: "id \<in> S"
    using expansion pp_b_exact_base_operators(1) by blast
  have child_xor: "pp_b_child_xor \<in> S"
    using expansion pp_b_child_xor_in_exact_stock by blast
  show ?thesis
    using identity child_xor closed witness
      pp_b_child_xor_surjective pp_b_child_xor_not_injective
    by (rule pp_b_surjective_noninjective_refutes_stock_L2)
qed

text \<open>
  The hypotheses are precisely the semantic consequences relevant to the
  proposed PP enlargement: the original closed logical operators remain
  pure, purity remains closed under composition, and a fundamental
  proposition supplies a \<open>fun\<acute>\<close> witness through QSS.  PP is not used.
  Consequently, within this tree architecture, adding PP cannot be the step
  that makes L2 valid.
\<close>

end
