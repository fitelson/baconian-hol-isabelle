theory Bacon_PP_ZF_Tree_Range_Diagonal
  imports Bacon_PP_ZF_Tree_Range_Classifier
begin

section \<open>Root equivalence is literal equality\<close>

lemma pp_t_root_eqv_imp_eq:
  assumes x: "Elem x (pp_t_domain \<sigma>)"
    and y: "Elem y (pp_t_domain \<sigma>)"
    and xy: "pp_t_eqv \<sigma> [] x y"
  shows "x = y"
  using x y xy
proof (induction \<sigma> arbitrary: x y)
  case Ind
  then show ?case by simp
next
  case Prop
  show ?case
  proof (rule pp_t_prop_ext[OF Prop.prems(1,2)])
    fix w
    show "pp_t_holds x w \<longleftrightarrow> pp_t_holds y w"
      using Prop.prems(3) by simp
  qed
next
  case (Arr \<sigma> \<tau>)
  have x_fun:
      "Elem x (Fun (pp_t_domain \<sigma>) (pp_t_domain \<tau>))"
    using pp_t_arrow_member_function[OF Arr.prems(1)] .
  have y_fun:
      "Elem y (Fun (pp_t_domain \<sigma>) (pp_t_domain \<tau>))"
    using pp_t_arrow_member_function[OF Arr.prems(2)] .
  obtain F where x_rep:
      "x = Lambda (pp_t_domain \<sigma>) F"
    using Elem_Fun_Lambda[OF x_fun] by blast
  obtain G where y_rep:
      "y = Lambda (pp_t_domain \<sigma>) G"
    using Elem_Fun_Lambda[OF y_fun] by blast
  have pointwise:
      "\<And>a. Elem a (pp_t_domain \<sigma>) \<Longrightarrow> F a = G a"
  proof -
    fix a
    assume a: "Elem a (pp_t_domain \<sigma>)"
    have aa: "pp_t_eqv \<sigma> [] a a"
      using pp_t_eqv_reflexive[OF a] .
    have apps:
        "pp_t_eqv \<tau> [] (x \<acute> a) (y \<acute> a)"
      using Arr.prems(3) a a aa by simp
    have xa: "Elem (x \<acute> a) (pp_t_domain \<tau>)"
      using pp_t_app_closed[OF Arr.prems(1) a] .
    have ya: "Elem (y \<acute> a) (pp_t_domain \<tau>)"
      using pp_t_app_closed[OF Arr.prems(2) a] .
    have app_eq: "x \<acute> a = y \<acute> a"
      using Arr.IH(2)[OF xa ya apps] .
    show "F a = G a"
      using app_eq a x_rep y_rep by (simp add: Lambda_app)
  qed
  show ?case
    using x_rep y_rep pointwise by (simp add: Lambda_ext)
qed

lemma pp_t_root_eqv_iff_eq:
  assumes x: "Elem x (pp_t_domain \<sigma>)"
    and y: "Elem y (pp_t_domain \<sigma>)"
  shows "pp_t_eqv \<sigma> [] x y \<longleftrightarrow> x = y"
proof
  assume "pp_t_eqv \<sigma> [] x y"
  show "x = y"
    using pp_t_root_eqv_imp_eq[OF x y] \<open>pp_t_eqv \<sigma> [] x y\<close> .
next
  assume "x = y"
  then show "pp_t_eqv \<sigma> [] x y"
    using pp_t_eqv_reflexive[OF x] by simp
qed

lemma pp_t_cone_invariant_prop_collapse:
  assumes P: "Elem P (pp_t_domain Prop)"
    and invariant: "\<And>s. pp_t_cone_rel Prop s P P"
  shows "P = pp_zf_truth (pp_t_holds P [])"
proof (rule pp_t_prop_ext[OF P pp_t_truth_in_domain])
  fix w
  have relation:
      "\<forall>u. pp_t_holds P (w @ u) \<longleftrightarrow>
        pp_t_holds P u"
    using invariant[of w] by simp
  have constancy:
      "pp_t_holds P (w @ []) \<longleftrightarrow> pp_t_holds P []"
    using relation[rule_format, of "[]"] .
  show "pp_t_holds P w
    \<longleftrightarrow>
    pp_t_holds (pp_zf_truth (pp_t_holds P [])) w"
    using constancy by simp
qed

context pp_t_stock_basis
begin

lemma pp_t_basis_stock_root_iff:
  "pp_t_basis_stock D \<sigma> [] x
    \<longleftrightarrow> x \<in> D \<sigma>"
proof
  assume stock: "pp_t_basis_stock D \<sigma> [] x"
  then obtain d where x: "Elem x (pp_t_domain \<sigma>)"
    and d: "d \<in> D \<sigma>"
    and xd: "pp_t_eqv \<sigma> [] x d"
    unfolding pp_t_basis_stock_def by blast
  have d_typed: "Elem d (pp_t_domain \<sigma>)"
    using basis_typed[OF d] .
  have "x = d"
    using pp_t_root_eqv_imp_eq[OF x d_typed xd] .
  then show "x \<in> D \<sigma>"
    using d by simp
next
  assume x: "x \<in> D \<sigma>"
  show "pp_t_basis_stock D \<sigma> [] x"
    using pp_t_basis_member_in_stock[OF x] .
qed

lemma pp_t_range_stock_root_iff:
  assumes E:
      "Elem E
        (pp_t_domain (Ind \<rightarrow>\<^sub>o pp_t_unary_type))"
  shows "pp_t_range_stock E [] X
    \<longleftrightarrow>
    X \<in> (\<lambda>n. E \<acute> n) `
      {n. Elem n (pp_t_domain Ind)}"
proof
  assume range: "pp_t_range_stock E [] X"
  then obtain n where X_typed:
      "Elem X (pp_t_domain pp_t_unary_type)"
    and n: "Elem n (pp_t_domain Ind)"
    and Xn: "pp_t_eqv pp_t_unary_type [] X (E \<acute> n)"
    unfolding pp_t_range_stock_def by blast
  have En_typed:
      "Elem (E \<acute> n) (pp_t_domain pp_t_unary_type)"
    using pp_t_app_closed[OF E n] .
  have "X = E \<acute> n"
    using pp_t_root_eqv_imp_eq[OF X_typed En_typed Xn] .
  then show "X \<in> (\<lambda>n. E \<acute> n) `
      {n. Elem n (pp_t_domain Ind)}"
    using n by blast
next
  assume image:
      "X \<in> (\<lambda>n. E \<acute> n) `
        {n. Elem n (pp_t_domain Ind)}"
  then obtain n where n: "Elem n (pp_t_domain Ind)"
    and X_def: "X = E \<acute> n"
    by blast
  have En_typed:
      "Elem (E \<acute> n) (pp_t_domain pp_t_unary_type)"
    using pp_t_app_closed[OF E n] .
  have En_refl:
      "pp_t_eqv pp_t_unary_type [] (E \<acute> n) (E \<acute> n)"
    using pp_t_eqv_reflexive[OF En_typed] .
  show "pp_t_range_stock E [] X"
    unfolding pp_t_range_stock_def
    using X_def En_typed n En_refl by blast
qed

theorem pp_t_range_complete_all_worlds_iff_root:
  assumes E:
      "Elem E
        (pp_t_domain (Ind \<rightarrow>\<^sub>o pp_t_unary_type))"
  shows "(\<forall>w X.
      pp_t_basis_stock D pp_t_unary_type w X
        \<longleftrightarrow> pp_t_range_stock E w X)
    \<longleftrightarrow>
    (\<forall>X.
      pp_t_basis_stock D pp_t_unary_type [] X
        \<longleftrightarrow> pp_t_range_stock E [] X)"
proof
  assume all:
      "\<forall>w X.
        pp_t_basis_stock D pp_t_unary_type w X
          \<longleftrightarrow> pp_t_range_stock E w X"
  show "\<forall>X.
      pp_t_basis_stock D pp_t_unary_type [] X
        \<longleftrightarrow> pp_t_range_stock E [] X"
    using all by blast
next
  assume root:
      "\<forall>X.
        pp_t_basis_stock D pp_t_unary_type [] X
          \<longleftrightarrow> pp_t_range_stock E [] X"
  have exact:
      "D pp_t_unary_type =
        (\<lambda>n. E \<acute> n) `
          {n. Elem n (pp_t_domain Ind)}"
  proof (rule set_eqI)
    fix X
    show "X \<in> D pp_t_unary_type
      \<longleftrightarrow>
      X \<in> (\<lambda>n. E \<acute> n) `
        {n. Elem n (pp_t_domain Ind)}"
    proof
      assume X: "X \<in> D pp_t_unary_type"
      have X_stock:
          "pp_t_basis_stock D pp_t_unary_type [] X"
        using pp_t_basis_member_in_stock[OF X] .
      have X_range: "pp_t_range_stock E [] X"
        using root X_stock by blast
      then obtain n where n: "Elem n (pp_t_domain Ind)"
        and Xn: "pp_t_eqv pp_t_unary_type [] X (E \<acute> n)"
        unfolding pp_t_range_stock_def by blast
      have X_typed: "Elem X (pp_t_domain pp_t_unary_type)"
        using basis_typed[OF X] .
      have En_typed:
          "Elem (E \<acute> n) (pp_t_domain pp_t_unary_type)"
        using pp_t_app_closed[OF E n] .
      have "X = E \<acute> n"
        using pp_t_root_eqv_imp_eq[OF X_typed En_typed Xn] .
      then show "X \<in> (\<lambda>n. E \<acute> n) `
          {n. Elem n (pp_t_domain Ind)}"
        using n by blast
    next
      assume X:
          "X \<in> (\<lambda>n. E \<acute> n) `
            {n. Elem n (pp_t_domain Ind)}"
      then obtain n where n: "Elem n (pp_t_domain Ind)"
        and X_def: "X = E \<acute> n"
        by blast
      have En_typed:
          "Elem (E \<acute> n) (pp_t_domain pp_t_unary_type)"
        using pp_t_app_closed[OF E n] .
      have En_refl:
          "pp_t_eqv pp_t_unary_type [] (E \<acute> n) (E \<acute> n)"
        using pp_t_eqv_reflexive[OF En_typed] .
      have X_range: "pp_t_range_stock E [] X"
        unfolding pp_t_range_stock_def
        using X_def En_typed n En_refl by blast
      have X_stock:
          "pp_t_basis_stock D pp_t_unary_type [] X"
        using root X_range by blast
      show "X \<in> D pp_t_unary_type"
        using X_stock pp_t_basis_stock_root_iff by blast
    qed
  qed
  show "\<forall>w X.
      pp_t_basis_stock D pp_t_unary_type w X
        \<longleftrightarrow> pp_t_range_stock E w X"
  proof (intro allI)
    fix w X
    show "pp_t_basis_stock D pp_t_unary_type w X
      \<longleftrightarrow> pp_t_range_stock E w X"
      unfolding pp_t_basis_stock_def pp_t_range_stock_def
      unfolding exact
      by blast
  qed
qed

theorem pp_t_range_complete_all_worlds_iff_exact_range:
  assumes E:
      "Elem E
        (pp_t_domain (Ind \<rightarrow>\<^sub>o pp_t_unary_type))"
  shows "(\<forall>w X.
      pp_t_basis_stock D pp_t_unary_type w X
        \<longleftrightarrow> pp_t_range_stock E w X)
    \<longleftrightarrow>
    D pp_t_unary_type =
      (\<lambda>n. E \<acute> n) `
        {n. Elem n (pp_t_domain Ind)}"
proof -
  have all_root:
      "(\<forall>w X.
          pp_t_basis_stock D pp_t_unary_type w X
            \<longleftrightarrow> pp_t_range_stock E w X)
      \<longleftrightarrow>
      (\<forall>X.
          pp_t_basis_stock D pp_t_unary_type [] X
            \<longleftrightarrow> pp_t_range_stock E [] X)"
    by (rule pp_t_range_complete_all_worlds_iff_root[OF E])
  have root_exact:
      "(\<forall>X.
          pp_t_basis_stock D pp_t_unary_type [] X
            \<longleftrightarrow> pp_t_range_stock E [] X)
      \<longleftrightarrow>
      D pp_t_unary_type =
        (\<lambda>n. E \<acute> n) `
          {n. Elem n (pp_t_domain Ind)}"
    unfolding set_eq_iff
    using pp_t_range_stock_root_iff[OF E]
      pp_t_basis_stock_root_iff[of pp_t_unary_type]
    by blast
  show ?thesis
    using all_root root_exact by blast
qed

lemma pp_t_basis_ind_prop_value_collapse:
  assumes P: "P \<in> D (Ind \<rightarrow>\<^sub>o Prop)"
    and n: "Elem n (pp_t_domain Ind)"
  shows "P \<acute> n =
    pp_zf_truth (pp_t_holds (P \<acute> n) [])"
proof (rule pp_t_cone_invariant_prop_collapse)
  have P_typed:
      "Elem P (pp_t_domain (Ind \<rightarrow>\<^sub>o Prop))"
    using basis_typed[OF P] .
  show "Elem (P \<acute> n) (pp_t_domain Prop)"
    using pp_t_app_closed[OF P_typed n] .
next
  fix s
  have P_cone:
      "pp_t_cone_rel (Ind \<rightarrow>\<^sub>o Prop) s P P"
    using basis_cone_natural[OF P] .
  have nn: "pp_t_cone_rel Ind s n n"
    by simp
  show "pp_t_cone_rel Prop s (P \<acute> n) (P \<acute> n)"
    using P_cone n n nn by simp
qed

end

section \<open>The exact typed obstruction to a range-complete enumerator\<close>

text \<open>
  A Cantor diagonal against an individual-indexed family of unary functions
  needs a way to feed the index of a function back to that function as a
  proposition.  At the present types this is not automatic: an index has type
  \<open>Ind\<close>, whereas a unary function expects an argument of type \<open>Prop\<close>.
  The following builder isolates the missing bridge as a map
  \<open>P : Ind \<rightarrow> Prop\<close>.
\<close>

definition pp_range_diagonal_builder :: oterm where
  "pp_range_diagonal_builder =
    Lam (Ind \<rightarrow>\<^sub>o pp_t_unary_type)
      (Lam (Ind \<rightarrow>\<^sub>o Prop)
        (Lam Prop
          (Forall Ind
            (Imp
              (Eq Prop (Var 1) (App (Var 2) (Var 0)))
              (Neg
                (App (App (Var 3) (Var 0)) (Var 1)))))))"

definition pp_t_index_separating ::
    "ZF \<Rightarrow> bool list \<Rightarrow> bool"
where
  "pp_t_index_separating P w \<longleftrightarrow>
    Elem P (pp_t_domain (Ind \<rightarrow>\<^sub>o Prop)) \<and>
    (\<forall>n m.
      Elem n (pp_t_domain Ind) \<longrightarrow>
      Elem m (pp_t_domain Ind) \<longrightarrow>
      pp_t_eqv Prop w (P \<acute> n) (P \<acute> m) \<longrightarrow>
      n = m)"

definition pp_t_index_reflecting ::
    "ZF \<Rightarrow> ZF \<Rightarrow> bool list \<Rightarrow> bool"
where
  "pp_t_index_reflecting E P w \<longleftrightarrow>
    Elem P (pp_t_domain (Ind \<rightarrow>\<^sub>o Prop)) \<and>
    (\<forall>n m.
      Elem n (pp_t_domain Ind) \<longrightarrow>
      Elem m (pp_t_domain Ind) \<longrightarrow>
      pp_t_eqv Prop w (P \<acute> n) (P \<acute> m) \<longrightarrow>
      pp_t_eqv pp_t_unary_type w (E \<acute> n) (E \<acute> m))"

abbreviation pp_t_range_diagonal :: "ZF \<Rightarrow> ZF \<Rightarrow> ZF" where
  "pp_t_range_diagonal E P \<equiv>
    (pp_t_closed_den pp_range_diagonal_builder \<acute> E) \<acute> P"

lemma pp_range_diagonal_builder_typed:
  "[] \<turnstile> pp_range_diagonal_builder :
    (Ind \<rightarrow>\<^sub>o pp_t_unary_type)
      \<rightarrow>\<^sub>o (Ind \<rightarrow>\<^sub>o Prop)
      \<rightarrow>\<^sub>o pp_t_unary_type"
  unfolding pp_range_diagonal_builder_def
  by (intro has_type.Lam has_type.Forall has_type.Imp
      has_type.Eq has_type.Neg has_type.App has_type.Var)
    (simp_all add: lookup_def)

lemma pp_range_diagonal_builder_logical:
  "pp_logical_vocabulary pp_range_diagonal_builder"
  unfolding pp_range_diagonal_builder_def
    pp_logical_vocabulary_def by simp

lemma pp_t_range_diagonal_in_domain:
  assumes E:
      "Elem E
        (pp_t_domain (Ind \<rightarrow>\<^sub>o pp_t_unary_type))"
    and P:
      "Elem P (pp_t_domain (Ind \<rightarrow>\<^sub>o Prop))"
  shows "Elem (pp_t_range_diagonal E P)
    (pp_t_domain pp_t_unary_type)"
proof -
  have builder:
      "Elem (pp_t_closed_den pp_range_diagonal_builder)
        (pp_t_domain
          ((Ind \<rightarrow>\<^sub>o pp_t_unary_type)
            \<rightarrow>\<^sub>o (Ind \<rightarrow>\<^sub>o Prop)
            \<rightarrow>\<^sub>o pp_t_unary_type))"
    using pp_t_closed_den_in_domain[
      OF pp_range_diagonal_builder_typed] .
  have first:
      "Elem
        (pp_t_closed_den pp_range_diagonal_builder \<acute> E)
        (pp_t_domain
          ((Ind \<rightarrow>\<^sub>o Prop)
            \<rightarrow>\<^sub>o pp_t_unary_type))"
    using pp_t_app_closed[OF builder E] .
  show ?thesis
    using pp_t_app_closed[OF first P] .
qed

lemma pp_t_range_diagonal_apply_holds:
  assumes E:
      "Elem E
        (pp_t_domain (Ind \<rightarrow>\<^sub>o pp_t_unary_type))"
    and P:
      "Elem P (pp_t_domain (Ind \<rightarrow>\<^sub>o Prop))"
    and q: "Elem q (pp_t_domain Prop)"
  shows "pp_t_holds ((pp_t_range_diagonal E P) \<acute> q) w
    \<longleftrightarrow>
    (\<forall>n. Elem n (pp_t_domain Ind) \<longrightarrow>
      (pp_t_eqv Prop w q (P \<acute> n) \<longrightarrow>
        \<not> pp_t_holds ((E \<acute> n) \<acute> q) w))"
proof -
  have env3:
      "\<And>n. extend_env n
        (extend_env q
          (extend_env P (extend_env E pp_t_closed_env))) 3 = E"
    by (simp add: numeral_3_eq_3)
  show ?thesis
    unfolding pp_t_closed_den_def pp_range_diagonal_builder_def
    using E P q
    by (simp add: Lambda_app pp_t_default_constants_def
        pp_t_closed_env_def extend_env.simps pp_t_app_closed env3)
qed

lemma pp_t_range_diagonal_at_code:
  assumes E:
      "Elem E
        (pp_t_domain (Ind \<rightarrow>\<^sub>o pp_t_unary_type))"
    and separating: "pp_t_index_separating P w"
    and k: "Elem k (pp_t_domain Ind)"
  shows "pp_t_holds
      ((pp_t_range_diagonal E P) \<acute> (P \<acute> k)) w
    \<longleftrightarrow>
    \<not> pp_t_holds ((E \<acute> k) \<acute> (P \<acute> k)) w"
proof -
  have P:
      "Elem P (pp_t_domain (Ind \<rightarrow>\<^sub>o Prop))"
    using separating unfolding pp_t_index_separating_def by blast
  have Pk: "Elem (P \<acute> k) (pp_t_domain Prop)"
    using pp_t_app_closed[OF P k] .
  have expansion:
      "pp_t_holds
          ((pp_t_range_diagonal E P) \<acute> (P \<acute> k)) w
      \<longleftrightarrow>
      (\<forall>n. Elem n (pp_t_domain Ind) \<longrightarrow>
        (pp_t_eqv Prop w (P \<acute> k) (P \<acute> n)
          \<longrightarrow>
          \<not> pp_t_holds ((E \<acute> n) \<acute> (P \<acute> k)) w))"
    by (rule pp_t_range_diagonal_apply_holds[OF E P Pk])
  have only_k:
      "\<And>n. Elem n (pp_t_domain Ind) \<Longrightarrow>
        pp_t_eqv Prop w (P \<acute> k) (P \<acute> n) \<Longrightarrow>
        n = k"
    using separating k
    unfolding pp_t_index_separating_def by blast
  have reflexive:
      "pp_t_eqv Prop w (P \<acute> k) (P \<acute> k)"
    using pp_t_eqv_reflexive[OF Pk] .
  show ?thesis
    using expansion only_k k reflexive by blast
qed

lemma pp_t_separating_imp_reflecting:
  assumes E:
      "Elem E
        (pp_t_domain (Ind \<rightarrow>\<^sub>o pp_t_unary_type))"
    and separating: "pp_t_index_separating P w"
  shows "pp_t_index_reflecting E P w"
proof (unfold pp_t_index_reflecting_def, intro conjI allI impI)
  show "Elem P (pp_t_domain (Ind \<rightarrow>\<^sub>o Prop))"
    using separating unfolding pp_t_index_separating_def by blast
next
  fix n m
  assume n: "Elem n (pp_t_domain Ind)"
    and m: "Elem m (pp_t_domain Ind)"
    and codes: "pp_t_eqv Prop w (P \<acute> n) (P \<acute> m)"
  have nm: "n = m"
    using separating n m codes
    unfolding pp_t_index_separating_def by blast
  have En:
      "Elem (E \<acute> n) (pp_t_domain pp_t_unary_type)"
    using pp_t_app_closed[OF E n] .
  have Em:
      "Elem (E \<acute> m) (pp_t_domain pp_t_unary_type)"
    using En nm by simp
  show
      "pp_t_eqv pp_t_unary_type w (E \<acute> n) (E \<acute> m)"
  proof (subst nm)
    show "pp_t_eqv pp_t_unary_type w (E \<acute> m) (E \<acute> m)"
      by (rule pp_t_eqv_reflexive[OF Em])
  qed
qed

lemma pp_t_range_diagonal_at_reflecting_code:
  assumes E:
      "Elem E
        (pp_t_domain (Ind \<rightarrow>\<^sub>o pp_t_unary_type))"
    and reflecting: "pp_t_index_reflecting E P w"
    and k: "Elem k (pp_t_domain Ind)"
  shows "pp_t_holds
      ((pp_t_range_diagonal E P) \<acute> (P \<acute> k)) w
    \<longleftrightarrow>
    \<not> pp_t_holds ((E \<acute> k) \<acute> (P \<acute> k)) w"
proof -
  have P:
      "Elem P (pp_t_domain (Ind \<rightarrow>\<^sub>o Prop))"
    using reflecting unfolding pp_t_index_reflecting_def by blast
  have Pk: "Elem (P \<acute> k) (pp_t_domain Prop)"
    using pp_t_app_closed[OF P k] .
  have expansion:
      "pp_t_holds
          ((pp_t_range_diagonal E P) \<acute> (P \<acute> k)) w
      \<longleftrightarrow>
      (\<forall>n. Elem n (pp_t_domain Ind) \<longrightarrow>
        (pp_t_eqv Prop w (P \<acute> k) (P \<acute> n)
          \<longrightarrow>
          \<not> pp_t_holds ((E \<acute> n) \<acute> (P \<acute> k)) w))"
    by (rule pp_t_range_diagonal_apply_holds[OF E P Pk])
  have reflexive:
      "pp_t_eqv Prop w (P \<acute> k) (P \<acute> k)"
    using pp_t_eqv_reflexive[OF Pk] .
  show ?thesis
  proof
    assume diagonal:
        "pp_t_holds
          ((pp_t_range_diagonal E P) \<acute> (P \<acute> k)) w"
    show "\<not> pp_t_holds ((E \<acute> k) \<acute> (P \<acute> k)) w"
      using expansion diagonal k reflexive by blast
  next
    assume not_k:
        "\<not> pp_t_holds ((E \<acute> k) \<acute> (P \<acute> k)) w"
    have universal:
        "\<forall>n. Elem n (pp_t_domain Ind) \<longrightarrow>
          (pp_t_eqv Prop w (P \<acute> k) (P \<acute> n)
            \<longrightarrow>
            \<not> pp_t_holds ((E \<acute> n) \<acute> (P \<acute> k)) w)"
    proof (intro allI impI)
      fix n
      assume n: "Elem n (pp_t_domain Ind)"
        and codes: "pp_t_eqv Prop w (P \<acute> k) (P \<acute> n)"
      have function_eqv:
          "pp_t_eqv pp_t_unary_type w (E \<acute> k) (E \<acute> n)"
        using reflecting k n codes
        unfolding pp_t_index_reflecting_def by blast
      have Pk_refl:
          "pp_t_eqv Prop w (P \<acute> k) (P \<acute> k)"
        using pp_t_eqv_reflexive[OF Pk] .
      have point_eqv:
          "pp_t_eqv Prop w
            ((E \<acute> k) \<acute> (P \<acute> k))
            ((E \<acute> n) \<acute> (P \<acute> k))"
        using pp_t_app_respects[
          OF function_eqv Pk Pk Pk_refl] .
      have truth:
          "pp_t_holds ((E \<acute> k) \<acute> (P \<acute> k)) w
          \<longleftrightarrow>
          pp_t_holds ((E \<acute> n) \<acute> (P \<acute> k)) w"
        using pp_t_prop_eqv_at[OF point_eqv, of w] by simp
      show "\<not> pp_t_holds ((E \<acute> n) \<acute> (P \<acute> k)) w"
        using truth not_k by blast
    qed
    show "pp_t_holds
        ((pp_t_range_diagonal E P) \<acute> (P \<acute> k)) w"
      using expansion universal by blast
  qed
qed

theorem pp_t_reflecting_map_refutes_range_completeness:
  assumes E:
      "Elem E
        (pp_t_domain (Ind \<rightarrow>\<^sub>o pp_t_unary_type))"
    and reflecting: "pp_t_index_reflecting E P w"
  shows "\<not> pp_t_range_stock E w (pp_t_range_diagonal E P)"
proof
  assume range:
      "pp_t_range_stock E w (pp_t_range_diagonal E P)"
  then obtain k where k: "Elem k (pp_t_domain Ind)"
    and diagonal_k:
      "pp_t_eqv pp_t_unary_type w
        (pp_t_range_diagonal E P) (E \<acute> k)"
    unfolding pp_t_range_stock_def by blast
  have P:
      "Elem P (pp_t_domain (Ind \<rightarrow>\<^sub>o Prop))"
    using reflecting unfolding pp_t_index_reflecting_def by blast
  have Pk: "Elem (P \<acute> k) (pp_t_domain Prop)"
    using pp_t_app_closed[OF P k] .
  have Pk_refl:
      "pp_t_eqv Prop w (P \<acute> k) (P \<acute> k)"
    using pp_t_eqv_reflexive[OF Pk] .
  have point:
      "pp_t_eqv Prop w
        ((pp_t_range_diagonal E P) \<acute> (P \<acute> k))
        ((E \<acute> k) \<acute> (P \<acute> k))"
    using diagonal_k Pk Pk Pk_refl by simp
  have same_truth:
      "pp_t_holds
          ((pp_t_range_diagonal E P) \<acute> (P \<acute> k)) w
      \<longleftrightarrow>
      pp_t_holds ((E \<acute> k) \<acute> (P \<acute> k)) w"
    using pp_t_prop_eqv_at[OF point, of w] by simp
  have opposite_truth:
      "pp_t_holds
      ((pp_t_range_diagonal E P) \<acute> (P \<acute> k)) w
      \<longleftrightarrow>
      \<not> pp_t_holds ((E \<acute> k) \<acute> (P \<acute> k)) w"
    by (rule pp_t_range_diagonal_at_reflecting_code[
      OF E reflecting k])
  show False
    using same_truth opposite_truth by blast
qed

corollary pp_t_separating_map_refutes_range_completeness:
  assumes E:
      "Elem E
        (pp_t_domain (Ind \<rightarrow>\<^sub>o pp_t_unary_type))"
    and separating: "pp_t_index_separating P w"
  shows "\<not> pp_t_range_stock E w (pp_t_range_diagonal E P)"
  using pp_t_reflecting_map_refutes_range_completeness[
    OF E pp_t_separating_imp_reflecting[OF E separating]] .

context pp_t_stock_basis
begin

theorem pp_t_range_complete_basis_has_no_reflecting_map:
  assumes E_stock:
      "pp_t_basis_stock D
        (Ind \<rightarrow>\<^sub>o pp_t_unary_type) w E"
    and P_stock:
      "pp_t_basis_stock D (Ind \<rightarrow>\<^sub>o Prop) w P"
    and reflecting: "pp_t_index_reflecting E P w"
    and range_complete:
      "\<And>X. pp_t_basis_stock D pp_t_unary_type w X
        \<longleftrightarrow> pp_t_range_stock E w X"
  shows False
proof -
  have builder_stock:
      "pp_t_basis_stock D
        ((Ind \<rightarrow>\<^sub>o pp_t_unary_type)
          \<rightarrow>\<^sub>o (Ind \<rightarrow>\<^sub>o Prop)
          \<rightarrow>\<^sub>o pp_t_unary_type)
        w (pp_t_closed_den pp_range_diagonal_builder)"
    using pp_t_basis_stock_contains_logical_den[
      OF pp_range_diagonal_builder_typed
        pp_range_diagonal_builder_logical] .
  have first_stock:
      "pp_t_basis_stock D
        ((Ind \<rightarrow>\<^sub>o Prop)
          \<rightarrow>\<^sub>o pp_t_unary_type)
        w (pp_t_closed_den pp_range_diagonal_builder \<acute> E)"
    using pp_t_basis_stock_application_closed[
      OF builder_stock E_stock] .
  have diagonal_stock:
      "pp_t_basis_stock D pp_t_unary_type w
        (pp_t_range_diagonal E P)"
    using pp_t_basis_stock_application_closed[
      OF first_stock P_stock] .
  have E:
      "Elem E
        (pp_t_domain (Ind \<rightarrow>\<^sub>o pp_t_unary_type))"
    using pp_t_basis_stock_typed[OF E_stock] .
  have diagonal_range:
      "pp_t_range_stock E w (pp_t_range_diagonal E P)"
    using range_complete diagonal_stock by blast
  show False
    using pp_t_reflecting_map_refutes_range_completeness[
      OF E reflecting] diagonal_range by blast
qed

corollary pp_t_range_complete_basis_has_no_separating_map:
  assumes E_stock:
      "pp_t_basis_stock D
        (Ind \<rightarrow>\<^sub>o pp_t_unary_type) w E"
    and P_stock:
      "pp_t_basis_stock D (Ind \<rightarrow>\<^sub>o Prop) w P"
    and separating: "pp_t_index_separating P w"
    and range_complete:
      "\<And>X. pp_t_basis_stock D pp_t_unary_type w X
        \<longleftrightarrow> pp_t_range_stock E w X"
  shows False
proof -
  have E:
      "Elem E
        (pp_t_domain (Ind \<rightarrow>\<^sub>o pp_t_unary_type))"
    using pp_t_basis_stock_typed[OF E_stock] .
  have reflecting: "pp_t_index_reflecting E P w"
    using pp_t_separating_imp_reflecting[OF E separating] .
  show False
    using pp_t_range_complete_basis_has_no_reflecting_map[
      OF E_stock P_stock reflecting range_complete] .
qed

end

end
