theory Bacon_PP_ZF_Goodman_L2_Model
  imports Bacon_PP_ZF_Tree_Stabilizer_Orbit
begin

section \<open>Goodman's L2 in Bacon's exact tree model\<close>

text \<open>
  We work with the exact Boolean operator stock induced by denotations of
  closed logical object-language terms.  Thus no ambient invariant operator
  is silently counted as pure.
\<close>

abbreviation pp_b_exact_stock :: "pp_b_operator set" where
  "pp_b_exact_stock \<equiv> pp_b_closed_logical_operator_stock"

definition pp_b_exact_fun_prime :: "pp_b_prop \<Rightarrow> bool" where
  "pp_b_exact_fun_prime p \<longleftrightarrow>
    (\<forall>X \<in> pp_b_exact_stock.
      \<forall>Y \<in> pp_b_exact_stock.
        X p = Y p \<longrightarrow> X = Y)"

definition pp_b_exact_reversible :: "pp_b_operator \<Rightarrow> bool" where
  "pp_b_exact_reversible Z \<longleftrightarrow>
    Z \<in> pp_b_exact_stock \<and>
    (\<exists>W \<in> pp_b_exact_stock.
      Z \<circ> W = id \<and> W \<circ> Z = id)"

definition pp_b_exact_G :: "pp_b_operator set" where
  "pp_b_exact_G = {Z. pp_b_exact_reversible Z}"

definition pp_b_exact_same_kind ::
    "pp_b_operator \<Rightarrow> pp_b_operator \<Rightarrow> bool" where
  "pp_b_exact_same_kind X Y \<longleftrightarrow>
    (\<exists>Z \<in> pp_b_exact_G. X = Y \<circ> Z)"

definition pp_b_exact_L2_pair ::
    "pp_b_operator \<Rightarrow> pp_b_operator \<Rightarrow> bool" where
  "pp_b_exact_L2_pair X Y \<longleftrightarrow>
    X \<in> pp_b_exact_stock \<and>
    Y \<in> pp_b_exact_stock \<and>
    (\<forall>p q.
      pp_b_exact_fun_prime p \<longrightarrow>
      pp_b_exact_fun_prime q \<longrightarrow>
      X p = Y q \<longrightarrow>
      pp_b_exact_same_kind X Y)"

definition pp_b_exact_L2 :: bool where
  "pp_b_exact_L2 \<longleftrightarrow>
    (\<forall>X \<in> pp_b_exact_stock.
      \<forall>Y \<in> pp_b_exact_stock.
        pp_b_exact_L2_pair X Y)"

lemma pp_b_exact_fun_primeI:
  assumes
    "\<And>X Y. X \<in> pp_b_exact_stock \<Longrightarrow>
      Y \<in> pp_b_exact_stock \<Longrightarrow>
      X p = Y p \<Longrightarrow> X = Y"
  shows "pp_b_exact_fun_prime p"
  using assms unfolding pp_b_exact_fun_prime_def by blast

lemma pp_b_exact_fun_primeD:
  assumes "pp_b_exact_fun_prime p"
    and "X \<in> pp_b_exact_stock"
    and "Y \<in> pp_b_exact_stock"
    and "X p = Y p"
  shows "X = Y"
  using assms unfolding pp_b_exact_fun_prime_def by blast

subsection \<open>Closed terms for the five base operators\<close>

definition pp_t_L2_identity_term :: oterm where
  "pp_t_L2_identity_term = Lam Prop (Var 0)"

definition pp_t_L2_truth_term :: oterm where
  "pp_t_L2_truth_term = Lam Prop ObjTrue"

definition pp_t_L2_falsity_term :: oterm where
  "pp_t_L2_falsity_term = Lam Prop ObjFalse"

definition pp_t_L2_box_term :: oterm where
  "pp_t_L2_box_term = Lam Prop (Eq Prop (Var 0) ObjTrue)"

definition pp_t_L2_diamond_term :: oterm where
  "pp_t_L2_diamond_term =
    Lam Prop (Neg (Eq Prop (Var 0) ObjFalse))"

lemma pp_t_L2_base_terms_typed:
  "[] \<turnstile> pp_t_L2_identity_term : (Prop \<rightarrow>\<^sub>o Prop)"
  "[] \<turnstile> pp_t_L2_truth_term : (Prop \<rightarrow>\<^sub>o Prop)"
  "[] \<turnstile> pp_t_L2_falsity_term : (Prop \<rightarrow>\<^sub>o Prop)"
  "[] \<turnstile> pp_t_L2_box_term : (Prop \<rightarrow>\<^sub>o Prop)"
  "[] \<turnstile> pp_t_L2_diamond_term : (Prop \<rightarrow>\<^sub>o Prop)"
  by (rule infer_type_sound;
      simp add: pp_t_L2_identity_term_def pp_t_L2_truth_term_def
        pp_t_L2_falsity_term_def pp_t_L2_box_term_def
        pp_t_L2_diamond_term_def ObjFalse_def ObjTrue_def lookup_def)+

lemma pp_t_L2_base_terms_logical:
  "pp_logical_vocabulary pp_t_L2_identity_term"
  "pp_logical_vocabulary pp_t_L2_truth_term"
  "pp_logical_vocabulary pp_t_L2_falsity_term"
  "pp_logical_vocabulary pp_t_L2_box_term"
  "pp_logical_vocabulary pp_t_L2_diamond_term"
  by (simp_all add: pp_logical_vocabulary_def
      pp_t_L2_identity_term_def pp_t_L2_truth_term_def
      pp_t_L2_falsity_term_def pp_t_L2_box_term_def
      pp_t_L2_diamond_term_def ObjFalse_def ObjTrue_def)

definition pp_b_const_true :: pp_b_operator where
  "pp_b_const_true = (\<lambda>P. UNIV)"

definition pp_b_const_false :: pp_b_operator where
  "pp_b_const_false = (\<lambda>P. {})"

lemma pp_b_operator_of_L2_identity:
  "pp_b_operator_of (pp_t_closed_den pp_t_L2_identity_term) = id"
proof (rule ext)
  fix P
  have p: "Elem (pp_zf_of_b P) (pp_t_domain Prop)"
    by (rule pp_zf_of_b_in_domain)
  have beta:
      "(pp_t_closed_den pp_t_L2_identity_term) \<acute> pp_zf_of_b P =
        pp_zf_of_b P"
    using p
    by (simp add: pp_t_closed_den_def
        pp_t_L2_identity_term_def Lambda_app)
  show "pp_b_operator_of (pp_t_closed_den pp_t_L2_identity_term) P =
      id P"
    unfolding pp_b_operator_of_def beta
    by simp
qed

lemma pp_b_operator_of_L2_truth:
  "pp_b_operator_of (pp_t_closed_den pp_t_L2_truth_term) =
    pp_b_const_true"
proof (rule ext, rule set_eqI)
  fix P w
  have p: "Elem (pp_zf_of_b P) (pp_t_domain Prop)"
    by (rule pp_zf_of_b_in_domain)
  have beta:
      "(pp_t_closed_den pp_t_L2_truth_term) \<acute> pp_zf_of_b P =
        pp_zf_truth True"
    using p
    by (simp add: pp_t_closed_den_def pp_t_L2_truth_term_def
        Lambda_app pp_t_eval_ObjTrue)
  show "w \<in> pp_b_operator_of
        (pp_t_closed_den pp_t_L2_truth_term) P
      \<longleftrightarrow> w \<in> pp_b_const_true P"
    unfolding pp_b_operator_of_def pp_b_of_zf_def
      pp_b_const_true_def beta
    by simp
qed

lemma pp_b_operator_of_L2_falsity:
  "pp_b_operator_of (pp_t_closed_den pp_t_L2_falsity_term) =
    pp_b_const_false"
proof (rule ext, rule set_eqI)
  fix P w
  have p: "Elem (pp_zf_of_b P) (pp_t_domain Prop)"
    by (rule pp_zf_of_b_in_domain)
  have beta:
      "\<not> pp_t_holds
        ((pp_t_closed_den pp_t_L2_falsity_term) \<acute>
          pp_zf_of_b P) w"
    using p
    by (simp add: pp_t_closed_den_def pp_t_L2_falsity_term_def
        ObjFalse_def Lambda_app pp_t_eval_ObjTrue)
  show "w \<in> pp_b_operator_of
        (pp_t_closed_den pp_t_L2_falsity_term) P
      \<longleftrightarrow> w \<in> pp_b_const_false P"
    unfolding pp_b_operator_of_def pp_b_of_zf_def
      pp_b_const_false_def
    using beta by simp
qed

lemma pp_b_operator_of_L2_box:
  "pp_b_operator_of (pp_t_closed_den pp_t_L2_box_term) = pp_b_box"
proof (rule ext, rule set_eqI)
  fix P w
  have p: "Elem (pp_zf_of_b P) (pp_t_domain Prop)"
    by (rule pp_zf_of_b_in_domain)
  have semantics:
      "pp_t_holds
        ((pp_t_closed_den pp_t_L2_box_term) \<acute>
          pp_zf_of_b P) w
        \<longleftrightarrow> w \<in> pp_b_box P"
    using p pp_t_zf_of_b_eqv_true_iff[of w P]
    by (simp add: pp_t_closed_den_def pp_t_L2_box_term_def
        Lambda_app pp_t_eval_ObjTrue)
  show "w \<in>
      pp_b_operator_of (pp_t_closed_den pp_t_L2_box_term) P
      \<longleftrightarrow> w \<in> pp_b_box P"
    unfolding pp_b_operator_of_def pp_b_of_zf_def
    using semantics by simp
qed

lemma pp_b_not_box_neg_iff_diamond:
  "w \<notin> pp_b_box (- P) \<longleftrightarrow> w \<in> pp_b_diamond P"
  unfolding pp_b_box_def pp_b_diamond_def
  by auto

lemma pp_t_future_mem_iff_diamond:
  "(\<exists>v. prefix w v \<and> v \<in> P) \<longleftrightarrow>
    w \<in> pp_b_diamond P"
  unfolding prefix_def pp_b_diamond_def
  by auto

lemma pp_b_operator_of_L2_diamond:
  "pp_b_operator_of (pp_t_closed_den pp_t_L2_diamond_term) =
    pp_b_diamond"
proof (rule ext, rule set_eqI)
  fix P w
  have p: "Elem (pp_zf_of_b P) (pp_t_domain Prop)"
    by (rule pp_zf_of_b_in_domain)
  have semantics:
      "pp_t_holds
        ((pp_t_closed_den pp_t_L2_diamond_term) \<acute>
          pp_zf_of_b P) w
        \<longleftrightarrow> w \<in> pp_b_diamond P"
    using p pp_t_zf_of_b_eqv_false_iff[of w P]
      pp_b_not_box_neg_iff_diamond[of w P]
      pp_t_future_mem_iff_diamond[of w P]
    by (simp add: pp_t_closed_den_def pp_t_L2_diamond_term_def
        ObjFalse_def Lambda_app pp_t_eval_ObjTrue)
  show "w \<in>
      pp_b_operator_of (pp_t_closed_den pp_t_L2_diamond_term) P
      \<longleftrightarrow> w \<in> pp_b_diamond P"
    unfolding pp_b_operator_of_def pp_b_of_zf_def
    using semantics by simp
qed

lemma pp_b_exact_stockI:
  assumes typed: "[] \<turnstile> M : (Prop \<rightarrow>\<^sub>o Prop)"
    and logical: "pp_logical_vocabulary M"
  shows "pp_b_operator_of (pp_t_closed_den M) \<in> pp_b_exact_stock"
proof -
  have den:
      "pp_t_closed_den M \<in> pp_t_exact_closed_logical_operators"
    unfolding pp_t_exact_closed_logical_operators_def
    using typed logical by blast
  show ?thesis
    unfolding pp_b_closed_logical_operator_stock_def
    using den by (rule imageI)
qed

lemma pp_b_exact_base_operators:
  "id \<in> pp_b_exact_stock"
  "pp_b_const_true \<in> pp_b_exact_stock"
  "pp_b_const_false \<in> pp_b_exact_stock"
  "pp_b_box \<in> pp_b_exact_stock"
  "pp_b_diamond \<in> pp_b_exact_stock"
proof -
  have identity:
      "pp_b_operator_of (pp_t_closed_den pp_t_L2_identity_term)
        \<in> pp_b_exact_stock"
    by (rule pp_b_exact_stockI[
          OF pp_t_L2_base_terms_typed(1)
            pp_t_L2_base_terms_logical(1)])
  show "id \<in> pp_b_exact_stock"
    using identity pp_b_operator_of_L2_identity by simp
next
  have truth:
      "pp_b_operator_of (pp_t_closed_den pp_t_L2_truth_term)
        \<in> pp_b_exact_stock"
    by (rule pp_b_exact_stockI[
          OF pp_t_L2_base_terms_typed(2)
            pp_t_L2_base_terms_logical(2)])
  show "pp_b_const_true \<in> pp_b_exact_stock"
    using truth pp_b_operator_of_L2_truth by simp
next
  have falsity:
      "pp_b_operator_of (pp_t_closed_den pp_t_L2_falsity_term)
        \<in> pp_b_exact_stock"
    by (rule pp_b_exact_stockI[
          OF pp_t_L2_base_terms_typed(3)
            pp_t_L2_base_terms_logical(3)])
  show "pp_b_const_false \<in> pp_b_exact_stock"
    using falsity pp_b_operator_of_L2_falsity by simp
next
  have box:
      "pp_b_operator_of (pp_t_closed_den pp_t_L2_box_term)
        \<in> pp_b_exact_stock"
    by (rule pp_b_exact_stockI[
          OF pp_t_L2_base_terms_typed(4)
            pp_t_L2_base_terms_logical(4)])
  show "pp_b_box \<in> pp_b_exact_stock"
    using box pp_b_operator_of_L2_box by simp
next
  have diamond:
      "pp_b_operator_of (pp_t_closed_den pp_t_L2_diamond_term)
        \<in> pp_b_exact_stock"
    by (rule pp_b_exact_stockI[
          OF pp_t_L2_base_terms_typed(5)
            pp_t_L2_base_terms_logical(5)])
  show "pp_b_diamond \<in> pp_b_exact_stock"
    using diamond pp_b_operator_of_L2_diamond by simp
qed

definition pp_b_complement :: pp_b_operator where
  "pp_b_complement = (\<lambda>P. - P)"

lemma pp_b_operator_of_negation:
  "pp_b_operator_of (pp_t_closed_den pp_negation_operator) =
    pp_b_complement"
proof (rule ext, rule set_eqI)
  fix P w
  have p: "Elem (pp_zf_of_b P) (pp_t_domain Prop)"
    by (rule pp_zf_of_b_in_domain)
  have beta:
      "(pp_t_closed_den pp_negation_operator) \<acute> pp_zf_of_b P =
        pp_t_eval pp_t_default_constants
          (extend_env (pp_zf_of_b P) pp_t_closed_env)
          (Neg (Var 0))"
    using p
    by (simp add: pp_t_closed_den_def pp_negation_operator_def
        Lambda_app)
  show "w \<in> pp_b_operator_of
        (pp_t_closed_den pp_negation_operator) P
      \<longleftrightarrow> w \<in> pp_b_complement P"
    unfolding pp_b_operator_of_def pp_b_of_zf_def
      pp_b_complement_def beta
    by simp
qed

lemma pp_b_exact_complement:
  "pp_b_complement \<in> pp_b_exact_stock"
proof -
  have typed:
      "[] \<turnstile> pp_negation_operator : (Prop \<rightarrow>\<^sub>o Prop)"
    using typed_pp_negation_operator
    by (simp add: pp_unary_ty_def)
  have logical: "pp_logical_vocabulary pp_negation_operator"
    by (simp add: pp_logical_vocabulary_def)
  have "pp_b_operator_of (pp_t_closed_den pp_negation_operator)
      \<in> pp_b_exact_stock"
    using typed logical by (rule pp_b_exact_stockI)
  then show ?thesis
    using pp_b_operator_of_negation by simp
qed

subsection \<open>Composition and the exact kind action\<close>

lemma pp_t_closed_den_compose:
  "pp_t_closed_den (pp_compose M N) =
    pp_t_qd_precompose (pp_t_closed_den M) (pp_t_closed_den N)"
  unfolding pp_t_closed_den_def pp_compose_def
    pp_t_qd_precompose_def
  by (simp add: fun_eq_iff pp_t_eval_shift)

lemma pp_b_operator_of_closed_den_compose:
  assumes M: "[] \<turnstile> M : (Prop \<rightarrow>\<^sub>o Prop)"
    and N: "[] \<turnstile> N : (Prop \<rightarrow>\<^sub>o Prop)"
  shows "pp_b_operator_of (pp_t_closed_den (pp_compose M N)) =
    pp_b_operator_of (pp_t_closed_den M) \<circ>
      pp_b_operator_of (pp_t_closed_den N)"
proof -
  have M_domain:
      "Elem (pp_t_closed_den M) (pp_t_domain pp_t_unary_type)"
    using pp_t_closed_den_in_domain[OF M] .
  have N_domain:
      "Elem (pp_t_closed_den N) (pp_t_domain pp_t_unary_type)"
    using pp_t_closed_den_in_domain[OF N] .
  show ?thesis
    unfolding pp_t_closed_den_compose
    using pp_b_operator_of_precompose[OF M_domain N_domain] .
qed

lemma pp_b_exact_stockE:
  assumes "F \<in> pp_b_exact_stock"
  obtains M where
    "[] \<turnstile> M : (Prop \<rightarrow>\<^sub>o Prop)"
    "pp_logical_vocabulary M"
    "F = pp_b_operator_of (pp_t_closed_den M)"
  using assms
  unfolding pp_b_closed_logical_operator_stock_def
    pp_t_exact_closed_logical_operators_def
  by blast

lemma pp_b_exact_stock_compose:
  assumes F: "F \<in> pp_b_exact_stock"
    and G: "G \<in> pp_b_exact_stock"
  shows "F \<circ> G \<in> pp_b_exact_stock"
proof -
  obtain M where M_type:
      "[] \<turnstile> M : (Prop \<rightarrow>\<^sub>o Prop)"
    and M_logical: "pp_logical_vocabulary M"
    and F_M: "F = pp_b_operator_of (pp_t_closed_den M)"
    using F by (rule pp_b_exact_stockE)
  obtain N where N_type:
      "[] \<turnstile> N : (Prop \<rightarrow>\<^sub>o Prop)"
    and N_logical: "pp_logical_vocabulary N"
    and G_N: "G = pp_b_operator_of (pp_t_closed_den N)"
    using G by (rule pp_b_exact_stockE)
  have M_unary: "[] \<turnstile> M : pp_unary_ty"
    using M_type by (simp add: pp_unary_ty_def)
  have N_unary: "[] \<turnstile> N : pp_unary_ty"
    using N_type by (simp add: pp_unary_ty_def)
  have compose_type:
      "[] \<turnstile> pp_compose M N : (Prop \<rightarrow>\<^sub>o Prop)"
    using typed_pp_compose[OF M_unary N_unary]
    by (simp add: pp_unary_ty_def)
  have compose_logical:
      "pp_logical_vocabulary (pp_compose M N)"
    using M_logical N_logical
    by (simp add: pp_logical_vocabulary_def pp_compose_def shift_def)
  have in_stock:
      "pp_b_operator_of (pp_t_closed_den (pp_compose M N))
        \<in> pp_b_exact_stock"
    using compose_type compose_logical by (rule pp_b_exact_stockI)
  show ?thesis
    using in_stock
      pp_b_operator_of_closed_den_compose[OF M_type N_type]
      F_M G_N
    by simp
qed

definition pp_b_possible_impossible :: pp_b_operator where
  "pp_b_possible_impossible P =
    pp_b_diamond (pp_b_box (- P))"

lemma pp_b_exact_diamond_box:
  "pp_b_diamond_box \<in> pp_b_exact_stock"
proof -
  have composition:
      "pp_b_diamond \<circ> pp_b_box \<in> pp_b_exact_stock"
    using pp_b_exact_base_operators(5,4)
    by (rule pp_b_exact_stock_compose)
  have "pp_b_diamond_box = pp_b_diamond \<circ> pp_b_box"
    by (rule ext)
      (simp add: pp_b_diamond_box_def)
  show ?thesis
    using composition \<open>pp_b_diamond_box =
      pp_b_diamond \<circ> pp_b_box\<close> by simp
qed

lemma pp_b_exact_possible_impossible:
  "pp_b_possible_impossible \<in> pp_b_exact_stock"
proof -
  have first:
      "pp_b_diamond \<circ> pp_b_box \<in> pp_b_exact_stock"
    using pp_b_exact_base_operators(5,4)
    by (rule pp_b_exact_stock_compose)
  have composition:
      "(pp_b_diamond \<circ> pp_b_box) \<circ> pp_b_complement
        \<in> pp_b_exact_stock"
    using first pp_b_exact_complement
    by (rule pp_b_exact_stock_compose)
  have "pp_b_possible_impossible =
      (pp_b_diamond \<circ> pp_b_box) \<circ> pp_b_complement"
    by (rule ext)
      (simp add: pp_b_possible_impossible_def
        pp_b_complement_def)
  show ?thesis
    using composition \<open>pp_b_possible_impossible =
      (pp_b_diamond \<circ> pp_b_box) \<circ> pp_b_complement\<close>
    by simp
qed

lemma pp_b_exact_G_id:
  "id \<in> pp_b_exact_G"
  unfolding pp_b_exact_G_def pp_b_exact_reversible_def
  using pp_b_exact_base_operators(1)
  by auto

lemma pp_b_exact_GE:
  assumes "Z \<in> pp_b_exact_G"
  obtains W where
    "Z \<in> pp_b_exact_stock"
    "W \<in> pp_b_exact_stock"
    "Z \<circ> W = id"
    "W \<circ> Z = id"
  using assms
  unfolding pp_b_exact_G_def pp_b_exact_reversible_def
  by blast

lemma pp_b_exact_G_inverse:
  assumes Z: "Z \<in> pp_b_exact_G"
    and W_stock: "W \<in> pp_b_exact_stock"
    and ZW: "Z \<circ> W = id"
    and WZ: "W \<circ> Z = id"
  shows "W \<in> pp_b_exact_G"
proof -
  have Z_stock: "Z \<in> pp_b_exact_stock"
    using Z by (rule pp_b_exact_GE)
  show ?thesis
    unfolding pp_b_exact_G_def pp_b_exact_reversible_def
    using W_stock Z_stock ZW WZ by blast
qed

lemma pp_b_exact_G_compose:
  assumes Z: "Z \<in> pp_b_exact_G"
    and W: "W \<in> pp_b_exact_G"
  shows "Z \<circ> W \<in> pp_b_exact_G"
proof -
  obtain Zi where Z_stock: "Z \<in> pp_b_exact_stock"
    and Zi_stock: "Zi \<in> pp_b_exact_stock"
    and ZZi: "Z \<circ> Zi = id"
    and ZiZ: "Zi \<circ> Z = id"
    using Z by (rule pp_b_exact_GE)
  obtain Wi where W_stock: "W \<in> pp_b_exact_stock"
    and Wi_stock: "Wi \<in> pp_b_exact_stock"
    and WWi: "W \<circ> Wi = id"
    and WiW: "Wi \<circ> W = id"
    using W by (rule pp_b_exact_GE)
  have ZW_stock: "Z \<circ> W \<in> pp_b_exact_stock"
    using Z_stock W_stock by (rule pp_b_exact_stock_compose)
  have WiZi_stock: "Wi \<circ> Zi \<in> pp_b_exact_stock"
    using Wi_stock Zi_stock by (rule pp_b_exact_stock_compose)
  have left: "(Z \<circ> W) \<circ> (Wi \<circ> Zi) = id"
  proof (rule ext)
    fix x
    have ww: "W (Wi (Zi x)) = Zi x"
      using fun_cong[OF WWi, of "Zi x"] by simp
    have zz: "Z (Zi x) = x"
      using fun_cong[OF ZZi, of x] by simp
    show "((Z \<circ> W) \<circ> (Wi \<circ> Zi)) x = id x"
      using ww zz by simp
  qed
  have right: "(Wi \<circ> Zi) \<circ> (Z \<circ> W) = id"
  proof (rule ext)
    fix x
    have zz: "Zi (Z (W x)) = W x"
      using fun_cong[OF ZiZ, of "W x"] by simp
    have ww: "Wi (W x) = x"
      using fun_cong[OF WiW, of x] by simp
    show "((Wi \<circ> Zi) \<circ> (Z \<circ> W)) x = id x"
      using zz ww by simp
  qed
  show ?thesis
    unfolding pp_b_exact_G_def pp_b_exact_reversible_def
    using ZW_stock WiZi_stock left right by blast
qed

lemma pp_b_exact_same_kind_refl:
  "pp_b_exact_same_kind X X"
proof (unfold pp_b_exact_same_kind_def, intro bexI[of _ id])
  show "X = X \<circ> id"
    by (rule ext) simp
  show "id \<in> pp_b_exact_G"
    by (rule pp_b_exact_G_id)
qed

lemma pp_b_exact_same_kind_sym:
  assumes "pp_b_exact_same_kind X Y"
  shows "pp_b_exact_same_kind Y X"
proof -
  obtain Z where Z_G: "Z \<in> pp_b_exact_G"
    and X: "X = Y \<circ> Z"
    using assms unfolding pp_b_exact_same_kind_def by blast
  obtain W where W_stock: "W \<in> pp_b_exact_stock"
    and ZW: "Z \<circ> W = id"
    and WZ: "W \<circ> Z = id"
    using Z_G by (rule pp_b_exact_GE)
  have W_G: "W \<in> pp_b_exact_G"
    using Z_G W_stock ZW WZ by (rule pp_b_exact_G_inverse)
  have Y: "Y = X \<circ> W"
  proof (rule ext)
    fix p
    have zw: "Z (W p) = p"
      using fun_cong[OF ZW, of p] by simp
    show "Y p = (X \<circ> W) p"
      unfolding X comp_apply
      using zw by simp
  qed
  show ?thesis
    unfolding pp_b_exact_same_kind_def
    using W_G Y by blast
qed

lemma pp_b_exact_same_kind_trans:
  assumes XY: "pp_b_exact_same_kind X Y"
    and YV: "pp_b_exact_same_kind Y V"
  shows "pp_b_exact_same_kind X V"
proof -
  obtain Z where Z_G: "Z \<in> pp_b_exact_G"
    and X: "X = Y \<circ> Z"
    using XY unfolding pp_b_exact_same_kind_def by blast
  obtain W where W_G: "W \<in> pp_b_exact_G"
    and Y: "Y = V \<circ> W"
    using YV unfolding pp_b_exact_same_kind_def by blast
  have WZ_G: "W \<circ> Z \<in> pp_b_exact_G"
    using W_G Z_G by (rule pp_b_exact_G_compose)
  have "X = V \<circ> (W \<circ> Z)"
    unfolding X Y by (simp add: fun_eq_iff)
  show ?thesis
    unfolding pp_b_exact_same_kind_def
    using WZ_G \<open>X = V \<circ> (W \<circ> Z)\<close> by blast
qed

theorem pp_b_exact_same_kind_equivp:
  "equivp pp_b_exact_same_kind"
proof (rule equivpI)
  show "reflp pp_b_exact_same_kind"
    by (rule reflpI, rule pp_b_exact_same_kind_refl)
  show "symp pp_b_exact_same_kind"
    by (rule sympI, rule pp_b_exact_same_kind_sym)
  show "transp pp_b_exact_same_kind"
    by (rule transpI, rule pp_b_exact_same_kind_trans)
qed

subsection \<open>Existence and elementary restrictions on fun-prime inputs\<close>

lemma pp_b_exact_stock_equivariant:
  assumes "F \<in> pp_b_exact_stock"
  shows "pp_b_equivariant F"
  using assms UnconditionalCone.pp_t_exact_closed_operator_equivariant
  unfolding pp_b_closed_logical_operator_stock_def by blast

theorem pp_b_exact_fun_prime_exists:
  "\<exists>p. pp_b_exact_fun_prime p"
proof -
  obtain p where separator:
      "\<forall>F \<in> pp_b_exact_stock.
        \<forall>G \<in> pp_b_exact_stock.
          (F p = G p \<longleftrightarrow> F = G)"
    using pp_b_generic_separator_for_countable_stock[
      OF pp_b_closed_logical_operator_stock_countable
        pp_b_exact_stock_equivariant] by blast
  show ?thesis
    using separator unfolding pp_b_exact_fun_prime_def by blast
qed

lemma pp_b_exact_fun_prime_not_top:
  assumes "pp_b_exact_fun_prime p"
  shows "p \<noteq> UNIV"
proof
  assume "p = UNIV"
  have agreement: "id p = pp_b_const_true p"
    using \<open>p = UNIV\<close> by (simp add: pp_b_const_true_def)
  have equality: "id = pp_b_const_true"
    using assms pp_b_exact_base_operators(1,2) agreement
    by (rule pp_b_exact_fun_primeD)
  have "id ({} :: pp_b_prop) = pp_b_const_true {}"
    using fun_cong[OF equality, of "{}"] .
  then show False
    by (simp add: pp_b_const_true_def)
qed

lemma pp_b_exact_fun_prime_not_bottom:
  assumes "pp_b_exact_fun_prime p"
  shows "p \<noteq> {}"
proof
  assume "p = {}"
  have agreement: "id p = pp_b_const_false p"
    using \<open>p = {}\<close> by (simp add: pp_b_const_false_def)
  have equality: "id = pp_b_const_false"
    using assms pp_b_exact_base_operators(1,3) agreement
    by (rule pp_b_exact_fun_primeD)
  have "id (UNIV :: pp_b_prop) = pp_b_const_false UNIV"
    using fun_cong[OF equality, of UNIV] .
  then show False
    by (simp add: pp_b_const_false_def)
qed

lemma pp_b_boxI:
  assumes "\<And>u. w @ u \<in> P"
  shows "w \<in> pp_b_box P"
  using assms unfolding pp_b_box_def by simp

lemma pp_b_boxD:
  assumes "w \<in> pp_b_box P"
  shows "w @ u \<in> P"
  using assms unfolding pp_b_box_def by simp

lemma pp_b_diamondI:
  assumes "w @ u \<in> P"
  shows "w \<in> pp_b_diamond P"
  using assms unfolding pp_b_diamond_def by blast

lemma pp_b_diamondE:
  assumes "w \<in> pp_b_diamond P"
  obtains u where "w @ u \<in> P"
  using assms unfolding pp_b_diamond_def by blast

lemma pp_b_box_idempotent:
  "pp_b_box (pp_b_box P) = pp_b_box P"
proof (rule set_eqI)
  fix w
  show "w \<in> pp_b_box (pp_b_box P) \<longleftrightarrow>
      w \<in> pp_b_box P"
  proof (rule iffI)
    assume twice: "w \<in> pp_b_box (pp_b_box P)"
    show "w \<in> pp_b_box P"
    proof (rule pp_b_boxI)
      fix u
      have at_root: "w @ [] \<in> pp_b_box P"
        using twice by (rule pp_b_boxD)
      have at_u: "(w @ []) @ u \<in> P"
        using at_root by (rule pp_b_boxD)
      show "w @ u \<in> P"
        using at_u by simp
    qed
  next
    assume once: "w \<in> pp_b_box P"
    show "w \<in> pp_b_box (pp_b_box P)"
    proof (rule pp_b_boxI)
      fix u
      show "w @ u \<in> pp_b_box P"
      proof (rule pp_b_boxI)
        fix v
        have at_uv: "w @ (u @ v) \<in> P"
          using once by (rule pp_b_boxD)
        show "(w @ u) @ v \<in> P"
          using at_uv by (simp only: append_assoc)
      qed
    qed
  qed
qed

lemma pp_b_diamond_idempotent:
  "pp_b_diamond (pp_b_diamond P) = pp_b_diamond P"
proof (rule set_eqI)
  fix w
  show "w \<in> pp_b_diamond (pp_b_diamond P) \<longleftrightarrow>
      w \<in> pp_b_diamond P"
  proof (rule iffI)
    assume twice: "w \<in> pp_b_diamond (pp_b_diamond P)"
    obtain u where future: "w @ u \<in> pp_b_diamond P"
      using twice by (rule pp_b_diamondE)
    obtain v where positive: "(w @ u) @ v \<in> P"
      using future by (rule pp_b_diamondE)
    show "w \<in> pp_b_diamond P"
    proof (rule pp_b_diamondI[where u="u @ v"])
      show "w @ (u @ v) \<in> P"
        using positive by (simp only: append_assoc)
    qed
  next
    assume once: "w \<in> pp_b_diamond P"
    show "w \<in> pp_b_diamond (pp_b_diamond P)"
    proof (rule pp_b_diamondI[where u="[]"])
      show "w @ [] \<in> pp_b_diamond P"
        using once by simp
    qed
  qed
qed

lemma pp_b_id_neq_box:
  "(id :: pp_b_operator) \<noteq> pp_b_box"
proof
  assume equality: "(id :: pp_b_operator) = pp_b_box"
  have root_id: "[] \<in> id ({[]} :: pp_b_prop)"
    by simp
  have root_not_box: "[] \<notin> pp_b_box ({[]} :: pp_b_prop)"
  proof
    assume root: "[] \<in> pp_b_box ({[]} :: pp_b_prop)"
    then have "[] @ [True] \<in> ({[]} :: pp_b_prop)"
      unfolding pp_b_box_def by blast
    then show False by simp
  qed
  have "id ({[]} :: pp_b_prop) = pp_b_box ({[]} :: pp_b_prop)"
    using fun_cong[OF equality, of "{[]}"] .
  then show False
    using root_id root_not_box by simp
qed

lemma pp_b_id_neq_diamond:
  "(id :: pp_b_operator) \<noteq> pp_b_diamond"
proof
  assume equality: "(id :: pp_b_operator) = pp_b_diamond"
  have root_not_id: "[] \<notin> id ({[True]} :: pp_b_prop)"
    by simp
  have root_diamond:
      "[] \<in> pp_b_diamond ({[True]} :: pp_b_prop)"
    unfolding pp_b_diamond_def
    by (intro CollectI exI[of _ "[True]"]) simp
  have "id ({[True]} :: pp_b_prop) =
      pp_b_diamond ({[True]} :: pp_b_prop)"
    using fun_cong[OF equality, of "{[True]}"] .
  then show False
    using root_not_id root_diamond by simp
qed

lemma pp_b_exact_fun_prime_not_box_fixed:
  assumes p: "pp_b_exact_fun_prime p"
  shows "pp_b_box p \<noteq> p"
proof
  assume fixed: "pp_b_box p = p"
  have agreement: "id p = pp_b_box p"
    using fixed by simp
  have equality: "(id :: pp_b_operator) = pp_b_box"
    using p pp_b_exact_base_operators(1,4) agreement
    by (rule pp_b_exact_fun_primeD)
  show False
    using pp_b_id_neq_box equality by contradiction
qed

lemma pp_b_exact_fun_prime_not_diamond_fixed:
  assumes p: "pp_b_exact_fun_prime p"
  shows "pp_b_diamond p \<noteq> p"
proof
  assume fixed: "pp_b_diamond p = p"
  have agreement: "id p = pp_b_diamond p"
    using fixed by simp
  have equality: "(id :: pp_b_operator) = pp_b_diamond"
    using p pp_b_exact_base_operators(1,5) agreement
    by (rule pp_b_exact_fun_primeD)
  show False
    using pp_b_id_neq_diamond equality by contradiction
qed

lemma pp_b_diamond_box_neq_const_false:
  "pp_b_diamond_box \<noteq> pp_b_const_false"
proof
  assume equality: "pp_b_diamond_box = pp_b_const_false"
  have left:
      "pp_b_diamond_box (UNIV :: pp_b_prop) = UNIV"
    by (rule set_eqI)
      (auto simp: pp_b_diamond_box_def pp_b_diamond_def
        pp_b_box_def)
  have right:
      "pp_b_const_false (UNIV :: pp_b_prop) = {}"
    by (simp add: pp_b_const_false_def)
  have "pp_b_diamond_box (UNIV :: pp_b_prop) =
      pp_b_const_false (UNIV :: pp_b_prop)"
    using fun_cong[OF equality, of UNIV] .
  then show False
    using left right by simp
qed

lemma pp_b_possible_impossible_neq_const_false:
  "pp_b_possible_impossible \<noteq> pp_b_const_false"
proof
  assume equality:
      "pp_b_possible_impossible = pp_b_const_false"
  have left:
      "pp_b_possible_impossible ({} :: pp_b_prop) = UNIV"
    by (rule set_eqI)
      (auto simp: pp_b_possible_impossible_def
        pp_b_diamond_def pp_b_box_def)
  have right:
      "pp_b_const_false ({} :: pp_b_prop) = {}"
    by (simp add: pp_b_const_false_def)
  have "pp_b_possible_impossible ({} :: pp_b_prop) =
      pp_b_const_false ({} :: pp_b_prop)"
    using fun_cong[OF equality, of "{}"] .
  then show False
    using left right by simp
qed

lemma pp_b_exact_fun_prime_box_nonbottom:
  assumes p: "pp_b_exact_fun_prime p"
  shows "pp_b_box p \<noteq> {}"
proof
  assume empty: "pp_b_box p = {}"
  have agreement:
      "pp_b_diamond_box p = pp_b_const_false p"
    using empty
    by (simp add: pp_b_diamond_box_def pp_b_diamond_def
        pp_b_const_false_def)
  have equality:
      "pp_b_diamond_box = pp_b_const_false"
    using p pp_b_exact_diamond_box
      pp_b_exact_base_operators(3) agreement
    by (rule pp_b_exact_fun_primeD)
  show False
    using pp_b_diamond_box_neq_const_false equality
    by contradiction
qed

lemma pp_b_possible_impossible_empty_if_diamond_top:
  assumes top: "pp_b_diamond p = UNIV"
  shows "pp_b_possible_impossible p = {}"
proof (rule set_eqI)
  fix w
  show "w \<in> pp_b_possible_impossible p \<longleftrightarrow> w \<in> {}"
  proof
    assume possible_impossible:
        "w \<in> pp_b_possible_impossible p"
    then obtain u where box:
        "w @ u \<in> pp_b_box (- p)"
      unfolding pp_b_possible_impossible_def pp_b_diamond_def
      by blast
    have possible: "w @ u \<in> pp_b_diamond p"
      using top by simp
    then obtain v where positive: "(w @ u) @ v \<in> p"
      unfolding pp_b_diamond_def by blast
    have negative: "(w @ u) @ v \<notin> p"
      using box
      unfolding pp_b_box_def
      by (simp add: append_assoc)
    show "w \<in> {}"
      using positive negative by contradiction
  next
    assume "w \<in> {}"
    then show "w \<in> pp_b_possible_impossible p"
      by simp
  qed
qed

lemma pp_b_exact_fun_prime_diamond_nontop:
  assumes p: "pp_b_exact_fun_prime p"
  shows "pp_b_diamond p \<noteq> UNIV"
proof
  assume top: "pp_b_diamond p = UNIV"
  have empty: "pp_b_possible_impossible p = {}"
    using top by (rule pp_b_possible_impossible_empty_if_diamond_top)
  have agreement:
      "pp_b_possible_impossible p = pp_b_const_false p"
    using empty by (simp add: pp_b_const_false_def)
  have equality:
      "pp_b_possible_impossible = pp_b_const_false"
    using p pp_b_exact_possible_impossible
      pp_b_exact_base_operators(3) agreement
    by (rule pp_b_exact_fun_primeD)
  show False
    using pp_b_possible_impossible_neq_const_false equality
    by contradiction
qed

subsection \<open>The necessity/possibility calibration\<close>

lemma pp_b_box_root_iff_top:
  "[] \<in> pp_b_box p \<longleftrightarrow> p = UNIV"
  unfolding pp_b_box_def
  by auto

lemma pp_b_diamond_root_iff_nonbottom:
  "[] \<in> pp_b_diamond p \<longleftrightarrow> p \<noteq> {}"
  unfolding pp_b_diamond_def
  by auto

lemma pp_b_exact_id_const_true_no_fun_prime_collision:
  assumes p: "pp_b_exact_fun_prime p"
  shows "id p \<noteq> pp_b_const_true q"
  using pp_b_exact_fun_prime_not_top[OF p]
  by (simp add: pp_b_const_true_def)

lemma pp_b_exact_id_const_false_no_fun_prime_collision:
  assumes p: "pp_b_exact_fun_prime p"
  shows "id p \<noteq> pp_b_const_false q"
  using pp_b_exact_fun_prime_not_bottom[OF p]
  by (simp add: pp_b_const_false_def)

lemma pp_b_exact_id_box_no_fun_prime_collision:
  assumes p: "pp_b_exact_fun_prime p"
  shows "id p \<noteq> pp_b_box q"
proof
  assume equality: "id p = pp_b_box q"
  have pq: "p = pp_b_box q"
    using equality by simp
  have fixed: "pp_b_box p = p"
    unfolding pq by (rule pp_b_box_idempotent)
  show False
    using pp_b_exact_fun_prime_not_box_fixed[OF p] fixed
    by contradiction
qed

lemma pp_b_exact_id_diamond_no_fun_prime_collision:
  assumes p: "pp_b_exact_fun_prime p"
  shows "id p \<noteq> pp_b_diamond q"
proof
  assume equality: "id p = pp_b_diamond q"
  have pq: "p = pp_b_diamond q"
    using equality by simp
  have fixed: "pp_b_diamond p = p"
    unfolding pq by (rule pp_b_diamond_idempotent)
  show False
    using pp_b_exact_fun_prime_not_diamond_fixed[OF p] fixed
    by contradiction
qed

lemma pp_b_const_true_const_false_no_collision:
  "pp_b_const_true p \<noteq> pp_b_const_false q"
  by (simp add: pp_b_const_true_def pp_b_const_false_def)

lemma pp_b_exact_const_true_box_no_fun_prime_collision:
  assumes q: "pp_b_exact_fun_prime q"
  shows "pp_b_const_true p \<noteq> pp_b_box q"
proof
  assume equality: "pp_b_const_true p = pp_b_box q"
  have box_top: "pp_b_box q = UNIV"
    using equality by (simp add: pp_b_const_true_def)
  have "q = UNIV"
    using box_top pp_b_box_root_iff_top[of q]
    by simp
  show False
    using pp_b_exact_fun_prime_not_top[OF q]
      \<open>q = UNIV\<close> by contradiction
qed

lemma pp_b_exact_const_true_diamond_no_fun_prime_collision:
  assumes q: "pp_b_exact_fun_prime q"
  shows "pp_b_const_true p \<noteq> pp_b_diamond q"
  using pp_b_exact_fun_prime_diamond_nontop[OF q]
  by (simp add: pp_b_const_true_def)

lemma pp_b_exact_const_false_box_no_fun_prime_collision:
  assumes q: "pp_b_exact_fun_prime q"
  shows "pp_b_const_false p \<noteq> pp_b_box q"
  using pp_b_exact_fun_prime_box_nonbottom[OF q]
  by (simp add: pp_b_const_false_def)

lemma pp_b_exact_const_false_diamond_no_fun_prime_collision:
  assumes q: "pp_b_exact_fun_prime q"
  shows "pp_b_const_false p \<noteq> pp_b_diamond q"
proof
  assume equality: "pp_b_const_false p = pp_b_diamond q"
  have diamond_empty: "pp_b_diamond q = {}"
    using equality by (simp add: pp_b_const_false_def)
  have "q = {}"
    using diamond_empty pp_b_diamond_root_iff_nonbottom[of q]
    by auto
  show False
    using pp_b_exact_fun_prime_not_bottom[OF q]
      \<open>q = {}\<close> by contradiction
qed

theorem pp_b_exact_box_diamond_no_fun_prime_collision:
  assumes p: "pp_b_exact_fun_prime p"
    and q: "pp_b_exact_fun_prime q"
  shows "pp_b_box p \<noteq> pp_b_diamond q"
proof
  assume equality: "pp_b_box p = pp_b_diamond q"
  have box_false: "[] \<notin> pp_b_box p"
    using pp_b_exact_fun_prime_not_top[OF p]
    by (simp add: pp_b_box_root_iff_top)
  have diamond_true: "[] \<in> pp_b_diamond q"
    using pp_b_exact_fun_prime_not_bottom[OF q]
    by (simp add: pp_b_diamond_root_iff_nonbottom)
  show False
    using equality box_false diamond_true by simp
qed

definition pp_b_L2_base_stock :: "pp_b_operator set" where
  "pp_b_L2_base_stock =
    {id, pp_b_const_true, pp_b_const_false, pp_b_box, pp_b_diamond}"

lemma pp_b_L2_base_stock_subset_exact:
  "pp_b_L2_base_stock \<subseteq> pp_b_exact_stock"
  unfolding pp_b_L2_base_stock_def
  using pp_b_exact_base_operators
  by auto

lemma pp_b_L2_base_stock_cases:
  assumes "X \<in> pp_b_L2_base_stock"
  obtains
      "X = id"
    | "X = pp_b_const_true"
    | "X = pp_b_const_false"
    | "X = pp_b_box"
    | "X = pp_b_diamond"
  using assms unfolding pp_b_L2_base_stock_def by auto

theorem pp_b_exact_base_collision_classification:
  assumes X: "X \<in> pp_b_L2_base_stock"
    and Y: "Y \<in> pp_b_L2_base_stock"
    and p: "pp_b_exact_fun_prime p"
    and q: "pp_b_exact_fun_prime q"
    and collision: "X p = Y q"
  shows "X = Y"
proof (rule pp_b_L2_base_stock_cases[OF X])
  assume X_id: "X = id"
  show ?thesis
  proof (rule pp_b_L2_base_stock_cases[OF Y])
    assume "Y = id"
    then show ?thesis using X_id by simp
  next
    assume Y_true: "Y = pp_b_const_true"
    show ?thesis
      using collision
        pp_b_exact_id_const_true_no_fun_prime_collision[OF p, of q]
      unfolding X_id Y_true by contradiction
  next
    assume Y_false: "Y = pp_b_const_false"
    show ?thesis
      using collision
        pp_b_exact_id_const_false_no_fun_prime_collision[OF p, of q]
      unfolding X_id Y_false by contradiction
  next
    assume Y_box: "Y = pp_b_box"
    show ?thesis
      using collision
        pp_b_exact_id_box_no_fun_prime_collision[OF p, of q]
      unfolding X_id Y_box by contradiction
  next
    assume Y_diamond: "Y = pp_b_diamond"
    show ?thesis
      using collision
        pp_b_exact_id_diamond_no_fun_prime_collision[OF p, of q]
      unfolding X_id Y_diamond by contradiction
  qed
next
  assume X_true: "X = pp_b_const_true"
  show ?thesis
  proof (rule pp_b_L2_base_stock_cases[OF Y])
    assume Y_id: "Y = id"
    show ?thesis
      using collision
        pp_b_exact_id_const_true_no_fun_prime_collision[OF q, of p]
      unfolding X_true Y_id by metis
  next
    assume "Y = pp_b_const_true"
    then show ?thesis using X_true by simp
  next
    assume Y_false: "Y = pp_b_const_false"
    show ?thesis
      using collision pp_b_const_true_const_false_no_collision[of p q]
      unfolding X_true Y_false by contradiction
  next
    assume Y_box: "Y = pp_b_box"
    show ?thesis
      using collision
        pp_b_exact_const_true_box_no_fun_prime_collision[OF q, of p]
      unfolding X_true Y_box by contradiction
  next
    assume Y_diamond: "Y = pp_b_diamond"
    show ?thesis
      using collision
        pp_b_exact_const_true_diamond_no_fun_prime_collision[OF q, of p]
      unfolding X_true Y_diamond by contradiction
  qed
next
  assume X_false: "X = pp_b_const_false"
  show ?thesis
  proof (rule pp_b_L2_base_stock_cases[OF Y])
    assume Y_id: "Y = id"
    show ?thesis
      using collision
        pp_b_exact_id_const_false_no_fun_prime_collision[OF q, of p]
      unfolding X_false Y_id by metis
  next
    assume Y_true: "Y = pp_b_const_true"
    show ?thesis
      using collision pp_b_const_true_const_false_no_collision[of q p]
      unfolding X_false Y_true by metis
  next
    assume "Y = pp_b_const_false"
    then show ?thesis using X_false by simp
  next
    assume Y_box: "Y = pp_b_box"
    show ?thesis
      using collision
        pp_b_exact_const_false_box_no_fun_prime_collision[OF q, of p]
      unfolding X_false Y_box by contradiction
  next
    assume Y_diamond: "Y = pp_b_diamond"
    show ?thesis
      using collision
        pp_b_exact_const_false_diamond_no_fun_prime_collision[OF q, of p]
      unfolding X_false Y_diamond by contradiction
  qed
next
  assume X_box: "X = pp_b_box"
  show ?thesis
  proof (rule pp_b_L2_base_stock_cases[OF Y])
    assume Y_id: "Y = id"
    show ?thesis
      using collision
        pp_b_exact_id_box_no_fun_prime_collision[OF q, of p]
      unfolding X_box Y_id by metis
  next
    assume Y_true: "Y = pp_b_const_true"
    show ?thesis
      using collision
        pp_b_exact_const_true_box_no_fun_prime_collision[OF p, of q]
      unfolding X_box Y_true by metis
  next
    assume Y_false: "Y = pp_b_const_false"
    show ?thesis
      using collision
        pp_b_exact_const_false_box_no_fun_prime_collision[OF p, of q]
      unfolding X_box Y_false by metis
  next
    assume "Y = pp_b_box"
    then show ?thesis using X_box by simp
  next
    assume Y_diamond: "Y = pp_b_diamond"
    show ?thesis
      using collision
        pp_b_exact_box_diamond_no_fun_prime_collision[OF p q]
      unfolding X_box Y_diamond by contradiction
  qed
next
  assume X_diamond: "X = pp_b_diamond"
  show ?thesis
  proof (rule pp_b_L2_base_stock_cases[OF Y])
    assume Y_id: "Y = id"
    show ?thesis
      using collision
        pp_b_exact_id_diamond_no_fun_prime_collision[OF q, of p]
      unfolding X_diamond Y_id by metis
  next
    assume Y_true: "Y = pp_b_const_true"
    show ?thesis
      using collision
        pp_b_exact_const_true_diamond_no_fun_prime_collision[OF p, of q]
      unfolding X_diamond Y_true by metis
  next
    assume Y_false: "Y = pp_b_const_false"
    show ?thesis
      using collision
        pp_b_exact_const_false_diamond_no_fun_prime_collision[OF p, of q]
      unfolding X_diamond Y_false by metis
  next
    assume Y_box: "Y = pp_b_box"
    show ?thesis
      using collision
        pp_b_exact_box_diamond_no_fun_prime_collision[OF q p]
      unfolding X_diamond Y_box by metis
  next
    assume "Y = pp_b_diamond"
    then show ?thesis using X_diamond by simp
  qed
qed

theorem pp_b_exact_L2_on_base:
  assumes X: "X \<in> pp_b_L2_base_stock"
    and Y: "Y \<in> pp_b_L2_base_stock"
  shows "pp_b_exact_L2_pair X Y"
proof (unfold pp_b_exact_L2_pair_def, intro conjI)
  show "X \<in> pp_b_exact_stock"
    using X pp_b_L2_base_stock_subset_exact by blast
  show "Y \<in> pp_b_exact_stock"
    using Y pp_b_L2_base_stock_subset_exact by blast
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
    have "X = Y"
      using X Y p q collision
      by (rule pp_b_exact_base_collision_classification)
    then show "pp_b_exact_same_kind X Y"
      using pp_b_exact_same_kind_refl by simp
  qed
qed

corollary pp_b_exact_L2_box_diamond:
  "pp_b_exact_L2_pair pp_b_box pp_b_diamond"
  by (rule pp_b_exact_L2_on_base)
    (simp_all add: pp_b_L2_base_stock_def)

lemma pp_b_exact_L2_pairD:
  assumes pair: "pp_b_exact_L2_pair X Y"
    and p: "pp_b_exact_fun_prime p"
    and q: "pp_b_exact_fun_prime q"
    and collision: "X p = Y q"
  shows "pp_b_exact_same_kind X Y"
  using assms unfolding pp_b_exact_L2_pair_def by blast

definition pp_b_exact_L2_counterexample ::
    "pp_b_operator \<Rightarrow> pp_b_operator \<Rightarrow>
      pp_b_prop \<Rightarrow> pp_b_prop \<Rightarrow> bool" where
  "pp_b_exact_L2_counterexample X Y p q \<longleftrightarrow>
    X \<in> pp_b_exact_stock \<and>
    Y \<in> pp_b_exact_stock \<and>
    pp_b_exact_fun_prime p \<and>
    pp_b_exact_fun_prime q \<and>
    X p = Y q \<and>
    \<not> pp_b_exact_same_kind X Y"

theorem pp_b_exact_not_L2_iff_counterexample:
  "\<not> pp_b_exact_L2 \<longleftrightarrow>
    (\<exists>X Y p q. pp_b_exact_L2_counterexample X Y p q)"
proof
  assume not_L2: "\<not> pp_b_exact_L2"
  then obtain X Y where X: "X \<in> pp_b_exact_stock"
    and Y: "Y \<in> pp_b_exact_stock"
    and not_pair: "\<not> pp_b_exact_L2_pair X Y"
    unfolding pp_b_exact_L2_def by blast
  then obtain p q where p: "pp_b_exact_fun_prime p"
    and q: "pp_b_exact_fun_prime q"
    and collision: "X p = Y q"
    and not_kind: "\<not> pp_b_exact_same_kind X Y"
    unfolding pp_b_exact_L2_pair_def by blast
  show "\<exists>X Y p q.
      pp_b_exact_L2_counterexample X Y p q"
    unfolding pp_b_exact_L2_counterexample_def
    using X Y p q collision not_kind by blast
next
  assume "\<exists>X Y p q.
      pp_b_exact_L2_counterexample X Y p q"
  then obtain X Y p q where counterexample:
      "pp_b_exact_L2_counterexample X Y p q"
    by blast
  have X: "X \<in> pp_b_exact_stock"
    and Y: "Y \<in> pp_b_exact_stock"
    and p: "pp_b_exact_fun_prime p"
    and q: "pp_b_exact_fun_prime q"
    and collision: "X p = Y q"
    and not_kind: "\<not> pp_b_exact_same_kind X Y"
    using counterexample
    unfolding pp_b_exact_L2_counterexample_def
    by blast+
  have not_pair: "\<not> pp_b_exact_L2_pair X Y"
    unfolding pp_b_exact_L2_pair_def
    using X Y p q collision not_kind by blast
  show "\<not> pp_b_exact_L2"
    unfolding pp_b_exact_L2_def
    using X Y not_pair by blast
qed

text \<open>
  This proves Goodman's advertised base calibration in the exact model:
  all twenty-five ordered pairs among identity, truth, falsity, necessity,
  and possibility satisfy semantic L2.
  It does not decide global L2: the remaining problem is to test all pairs
  in the countable closed-logical stock, especially cross-input collisions
  between operators not related by a closed-logical reversible.
\<close>

end
