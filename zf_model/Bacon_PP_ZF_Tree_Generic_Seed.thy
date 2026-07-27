theory Bacon_PP_ZF_Tree_Generic_Seed
  imports Bacon_PP_ZF_Tree_Logical_Stock
begin

section \<open>A countable generic witness on the Boolean-prefix tree\<close>

type_synonym pp_b_prop = "bool list set"
type_synonym pp_b_operator = "pp_b_prop \<Rightarrow> pp_b_prop"

definition pp_b_view ::
    "bool list \<Rightarrow> pp_b_prop \<Rightarrow> pp_b_prop" where
  "pp_b_view s P = {u. s @ u \<in> P}"

definition pp_b_lift ::
    "bool list \<Rightarrow> pp_b_prop \<Rightarrow> pp_b_prop" where
  "pp_b_lift s P = {s @ u |u. u \<in> P}"

definition pp_b_equivariant :: "pp_b_operator \<Rightarrow> bool" where
  "pp_b_equivariant F \<longleftrightarrow>
    (\<forall>s P. pp_b_view s (F P) = F (pp_b_view s P))"

definition pp_b_root_unary_recombination ::
    "pp_b_operator \<Rightarrow> pp_b_prop \<Rightarrow> bool" where
  "pp_b_root_unary_recombination F R \<longleftrightarrow>
    ((\<forall>w. w \<in> F R) \<longrightarrow>
      (\<forall>P. [] \<in> F P))"

lemma pp_b_view_root[simp]:
  "pp_b_view [] P = P"
  by (auto simp: pp_b_view_def)

lemma pp_b_view_compose:
  "pp_b_view s (pp_b_view t P) = pp_b_view (t @ s) P"
  by (auto simp: pp_b_view_def append_assoc)

lemma pp_b_view_lift[simp]:
  "pp_b_view s (pp_b_lift s P) = P"
  by (auto simp: pp_b_view_def pp_b_lift_def)

lemma pp_b_view_membership_root[simp]:
  "[] \<in> pp_b_view s P \<longleftrightarrow> s \<in> P"
  by (simp add: pp_b_view_def)

fun pp_b_code :: "nat \<Rightarrow> bool list" where
  "pp_b_code 0 = [True]"
| "pp_b_code (Suc n) = False # pp_b_code n"

lemma pp_b_code_append_eq[simp]:
  "pp_b_code n @ u = pp_b_code m @ v
    \<longleftrightarrow> n = m \<and> u = v"
proof (induction n arbitrary: m u v)
  case 0
  then show ?case
    by (cases m) auto
next
  case (Suc n)
  then show ?case
    by (cases m) auto
qed

definition pp_b_generic_witness ::
    "(nat \<Rightarrow> pp_b_prop) \<Rightarrow> pp_b_prop" where
  "pp_b_generic_witness q =
    (\<Union>n. pp_b_lift (pp_b_code n) (q n))"

lemma pp_b_generic_witness_mem:
  "w \<in> pp_b_generic_witness q
    \<longleftrightarrow>
    (\<exists>n u. w = pp_b_code n @ u \<and> u \<in> q n)"
  by (auto simp: pp_b_generic_witness_def pp_b_lift_def)

theorem pp_b_view_generic_witness[simp]:
  "pp_b_view (pp_b_code n) (pp_b_generic_witness q) = q n"
proof (rule set_eqI)
  fix u
  show "u \<in> pp_b_view (pp_b_code n) (pp_b_generic_witness q)
      \<longleftrightarrow> u \<in> q n"
    unfolding pp_b_view_def pp_b_generic_witness_mem
    by auto
qed

definition pp_b_counterexample_choice ::
    "(nat \<Rightarrow> pp_b_operator) \<Rightarrow> nat \<Rightarrow> pp_b_prop"
  where
  "pp_b_counterexample_choice E n =
    (if \<forall>P. [] \<in> E n P
     then {}
     else (SOME P. [] \<notin> E n P))"

lemma pp_b_counterexample_choice_falsifies:
  assumes nonuniversal: "\<not> (\<forall>P. [] \<in> E n P)"
  shows "[] \<notin> E n (pp_b_counterexample_choice E n)"
proof -
  have exists: "\<exists>P. [] \<notin> E n P"
    using nonuniversal by blast
  show ?thesis
    unfolding pp_b_counterexample_choice_def
    using nonuniversal someI_ex[OF exists] by simp
qed

theorem pp_b_generic_witness_for_sequence:
  fixes E :: "nat \<Rightarrow> pp_b_operator"
  assumes equivariant: "\<And>n. pp_b_equivariant (E n)"
  shows "\<exists>R. \<forall>n. pp_b_root_unary_recombination (E n) R"
proof -
  let ?q = "pp_b_counterexample_choice E"
  let ?R = "pp_b_generic_witness ?q"
  have recombines:
      "pp_b_root_unary_recombination (E n) ?R" for n
  proof (unfold pp_b_root_unary_recombination_def, intro impI)
    assume necessary: "\<forall>w. w \<in> E n ?R"
    show "\<forall>P. [] \<in> E n P"
    proof (rule ccontr)
      assume nonuniversal: "\<not> (\<forall>P. [] \<in> E n P)"
      have false_choice: "[] \<notin> E n (?q n)"
        using pp_b_counterexample_choice_falsifies[
          where E=E and n=n, OF nonuniversal] .
      have view_operator:
          "pp_b_view (pp_b_code n) (E n ?R) =
            E n (pp_b_view (pp_b_code n) ?R)"
        using equivariant[of n]
        unfolding pp_b_equivariant_def by blast
      have at_code: "pp_b_code n \<in> E n ?R"
        using necessary by blast
      have root_view:
          "[] \<in> pp_b_view (pp_b_code n) (E n ?R)"
        using at_code by simp
      have "[] \<in> E n (?q n)"
        using root_view view_operator by simp
      then show False
        using false_choice by blast
    qed
  qed
  show ?thesis
    using recombines by blast
qed

theorem pp_b_generic_witness_for_countable_stock:
  fixes Stock :: "pp_b_operator set"
  assumes countable: "countable Stock"
    and equivariant: "\<And>F. F \<in> Stock \<Longrightarrow> pp_b_equivariant F"
  shows "\<exists>R. \<forall>F \<in> Stock.
    pp_b_root_unary_recombination F R"
proof (cases "Stock = {}")
  case True
  then show ?thesis by simp
next
  case False
  let ?E = "from_nat_into Stock"
  have range: "range ?E = Stock"
    using False countable by (rule range_from_nat_into)
  have E_mem: "?E n \<in> Stock" for n
    using range by blast
  have E_equivariant: "pp_b_equivariant (?E n)" for n
    using E_mem by (rule equivariant)
  have existence:
      "\<exists>R. \<forall>n. pp_b_root_unary_recombination (?E n) R"
    by (rule pp_b_generic_witness_for_sequence)
      (rule E_equivariant)
  let ?R = "SOME R.
    \<forall>n. pp_b_root_unary_recombination (?E n) R"
  have sequence:
      "\<forall>n. pp_b_root_unary_recombination (?E n) ?R"
    using someI_ex[OF existence] .
  show ?thesis
  proof (intro exI[of _ ?R] ballI)
    fix F
    assume F_mem: "F \<in> Stock"
    have F_range: "F \<in> range ?E"
      using F_mem range by simp
    show "pp_b_root_unary_recombination F ?R"
      using sequence F_range by auto
  qed
qed

theorem pp_b_generic_separator_for_countable_stock:
  fixes Stock :: "pp_b_operator set"
  assumes countable: "countable Stock"
    and equivariant:
      "\<And>F. F \<in> Stock \<Longrightarrow> pp_b_equivariant F"
  shows "\<exists>R. \<forall>F \<in> Stock. \<forall>G \<in> Stock.
    (F R = G R \<longleftrightarrow> F = G)"
proof (cases "Stock = {}")
  case True
  then show ?thesis by simp
next
  case False
  let ?Pairs = "Stock \<times> Stock"
  let ?E = "from_nat_into ?Pairs"
  have pairs_countable: "countable ?Pairs"
    using countable by simp
  have pairs_nonempty: "?Pairs \<noteq> {}"
    using False by blast
  have range: "range ?E = ?Pairs"
    using pairs_nonempty pairs_countable
    by (rule range_from_nat_into)
  let ?Q =
    "\<lambda>n.
      (if fst (?E n) = snd (?E n)
       then {}
       else SOME P. fst (?E n) P \<noteq> snd (?E n) P)"
  have Q_separates:
      "fst (?E n) \<noteq> snd (?E n) \<Longrightarrow>
        fst (?E n) (?Q n) \<noteq> snd (?E n) (?Q n)"
    for n
  proof -
    assume distinct: "fst (?E n) \<noteq> snd (?E n)"
    have witness:
        "\<exists>P. fst (?E n) P \<noteq> snd (?E n) P"
      using distinct by (auto simp: fun_eq_iff)
    show ?thesis
      using distinct someI_ex[OF witness] by simp
  qed
  let ?R = "pp_b_generic_witness ?Q"
  have separates:
      "F \<in> Stock \<Longrightarrow> G \<in> Stock \<Longrightarrow>
        F ?R = G ?R \<Longrightarrow> F = G"
    for F G
  proof (rule ccontr)
    assume F: "F \<in> Stock"
      and G: "G \<in> Stock"
      and outputs: "F ?R = G ?R"
      and distinct: "F \<noteq> G"
    have pair: "(F, G) \<in> ?Pairs"
      using F G by simp
    have pair_range: "(F, G) \<in> range ?E"
      using pair range by simp
    from pair_range obtain n where pair_n_rev: "(F, G) = ?E n"
      by auto
    have pair_n: "?E n = (F, G)"
      using pair_n_rev by simp
    have Q_distinct: "F (?Q n) \<noteq> G (?Q n)"
      using Q_separates[of n] distinct
      unfolding pair_n by simp
    have F_view:
        "pp_b_view (pp_b_code n) (F ?R) = F (?Q n)"
      using equivariant[OF F]
      unfolding pp_b_equivariant_def by simp
    have G_view:
        "pp_b_view (pp_b_code n) (G ?R) = G (?Q n)"
      using equivariant[OF G]
      unfolding pp_b_equivariant_def by simp
    show False
      using outputs F_view G_view Q_distinct by simp
  qed
  show ?thesis
  proof (intro exI[of _ ?R] ballI allI impI iffI)
    fix F G
    assume F: "F \<in> Stock"
      and G: "G \<in> Stock"
      and outputs: "F ?R = G ?R"
    show "F = G"
      using separates[OF F G outputs] .
  next
    fix F G
    assume F: "F \<in> Stock"
      and G: "G \<in> Stock"
      and "F = G"
    then show "F ?R = G ?R"
      by simp
  qed
qed

section \<open>The exact closed-logical operator stock\<close>

definition pp_b_of_zf :: "ZF \<Rightarrow> pp_b_prop" where
  "pp_b_of_zf P = {w. pp_t_holds P w}"

definition pp_zf_of_b :: "pp_b_prop \<Rightarrow> ZF" where
  "pp_zf_of_b P = pp_t_prop (\<lambda>w. w \<in> P)"

lemma pp_t_holds_zf_of_b[simp]:
  "pp_t_holds (pp_zf_of_b P) w \<longleftrightarrow> w \<in> P"
  by (simp add: pp_zf_of_b_def)

lemma pp_b_of_zf_of_b[simp]:
  "pp_b_of_zf (pp_zf_of_b P) = P"
  by (auto simp: pp_b_of_zf_def pp_zf_of_b_def)

lemma pp_zf_of_b_in_domain:
  "Elem (pp_zf_of_b P) (pp_t_domain Prop)"
  unfolding pp_zf_of_b_def
  by (rule pp_t_prop_in_domain)

lemma pp_zf_of_b_of_zf:
  assumes P: "Elem P (pp_t_domain Prop)"
  shows "pp_zf_of_b (pp_b_of_zf P) = P"
proof (rule pp_t_prop_ext)
  show "Elem (pp_zf_of_b (pp_b_of_zf P)) (pp_t_domain Prop)"
    by (rule pp_zf_of_b_in_domain)
  show "Elem P (pp_t_domain Prop)"
    using P .
  show "\<And>w. pp_t_holds (pp_zf_of_b (pp_b_of_zf P)) w =
      pp_t_holds P w"
    by (simp add: pp_zf_of_b_def pp_b_of_zf_def)
qed

definition pp_b_operator_of :: "ZF \<Rightarrow> pp_b_operator" where
  "pp_b_operator_of X P =
    pp_b_of_zf (X \<acute> pp_zf_of_b P)"

definition pp_t_exact_closed_logical_operators :: "ZF set" where
  "pp_t_exact_closed_logical_operators =
    {X. \<exists>M.
      [] \<turnstile> M : (Prop \<rightarrow>\<^sub>o Prop) \<and>
      pp_logical_vocabulary M \<and>
      X = pp_t_closed_den M}"

definition pp_b_closed_logical_operator_stock ::
    "pp_b_operator set" where
  "pp_b_closed_logical_operator_stock =
    pp_b_operator_of ` pp_t_exact_closed_logical_operators"

lemma pp_t_exact_closed_logical_operators_countable:
  "countable pp_t_exact_closed_logical_operators"
proof -
  let ?Terms =
    "{M. [] \<turnstile> M : (Prop \<rightarrow>\<^sub>o Prop) \<and>
      pp_logical_vocabulary M}"
  have terms_countable: "countable ?Terms"
    by simp
  have representation:
      "pp_t_exact_closed_logical_operators =
        pp_t_closed_den ` ?Terms"
    unfolding pp_t_exact_closed_logical_operators_def
    by auto
  show ?thesis
    unfolding representation
    using terms_countable by (rule countable_image)
qed

lemma pp_b_closed_logical_operator_stock_countable:
  "countable pp_b_closed_logical_operator_stock"
  unfolding pp_b_closed_logical_operator_stock_def
  using pp_t_exact_closed_logical_operators_countable
  by (rule countable_image)

lemma pp_t_exact_closed_logical_operator_in_domain:
  assumes "X \<in> pp_t_exact_closed_logical_operators"
  shows "Elem X (pp_t_domain (Prop \<rightarrow>\<^sub>o Prop))"
  using assms pp_t_closed_den_in_domain
  unfolding pp_t_exact_closed_logical_operators_def
  by blast

lemma pp_b_recombination_transfers_to_zf:
  assumes recombines:
      "pp_b_root_unary_recombination (pp_b_operator_of X) R"
    and necessary:
      "\<forall>w. pp_t_holds (X \<acute> pp_zf_of_b R) w"
  shows "\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
    pp_t_holds (X \<acute> q) []"
proof (intro allI impI)
  fix q
  assume q: "Elem q (pp_t_domain Prop)"
  have abstract_necessary:
      "\<forall>w. w \<in> pp_b_operator_of X R"
    using necessary
    by (simp add: pp_b_operator_of_def pp_b_of_zf_def)
  have abstract_universal:
      "\<forall>P. [] \<in> pp_b_operator_of X P"
    using recombines abstract_necessary
    unfolding pp_b_root_unary_recombination_def by blast
  have at_q:
      "[] \<in> pp_b_operator_of X (pp_b_of_zf q)"
    using abstract_universal by blast
  show "pp_t_holds (X \<acute> q) []"
    using at_q pp_zf_of_b_of_zf[OF q]
    by (simp add: pp_b_operator_of_def pp_b_of_zf_def)
qed

section \<open>Equivariance of the known logical obstructions\<close>

definition pp_b_box :: "pp_b_operator" where
  "pp_b_box P = {w. \<forall>u. w @ u \<in> P}"

definition pp_b_diamond :: "pp_b_operator" where
  "pp_b_diamond P = {w. \<exists>u. w @ u \<in> P}"

definition pp_b_not_box :: "pp_b_operator" where
  "pp_b_not_box P = - pp_b_box P"

definition pp_b_diamond_box :: "pp_b_operator" where
  "pp_b_diamond_box P = pp_b_diamond (pp_b_box P)"

definition pp_b_settles :: "pp_b_operator" where
  "pp_b_settles P =
    pp_b_diamond (pp_b_box P) \<union>
    pp_b_diamond (pp_b_box (- P))"

lemma pp_b_box_equivariant:
  "pp_b_equivariant pp_b_box"
  unfolding pp_b_equivariant_def pp_b_view_def pp_b_box_def
  apply (intro allI)
  apply (rule set_eqI)
  by (auto simp: append_assoc)

lemma pp_b_diamond_equivariant:
  "pp_b_equivariant pp_b_diamond"
  unfolding pp_b_equivariant_def pp_b_view_def pp_b_diamond_def
  apply (intro allI)
  apply (rule set_eqI)
  by (auto simp: append_assoc)

lemma pp_b_view_complement:
  "pp_b_view s (- P) = - pp_b_view s P"
  by (auto simp: pp_b_view_def)

lemma pp_b_view_union:
  "pp_b_view s (P \<union> Q) =
    pp_b_view s P \<union> pp_b_view s Q"
  by (auto simp: pp_b_view_def)

lemma pp_b_not_box_equivariant:
  "pp_b_equivariant pp_b_not_box"
  using pp_b_box_equivariant
  unfolding pp_b_equivariant_def pp_b_not_box_def
    pp_b_view_def
  by auto

lemma pp_b_diamond_box_equivariant:
  "pp_b_equivariant pp_b_diamond_box"
proof (unfold pp_b_equivariant_def, intro allI)
  fix s P
  have diamond:
      "pp_b_view s (pp_b_diamond (pp_b_box P)) =
        pp_b_diamond (pp_b_view s (pp_b_box P))"
    using pp_b_diamond_equivariant
    unfolding pp_b_equivariant_def by blast
  have box:
      "pp_b_view s (pp_b_box P) =
        pp_b_box (pp_b_view s P)"
    using pp_b_box_equivariant
    unfolding pp_b_equivariant_def by blast
  show "pp_b_view s (pp_b_diamond_box P) =
      pp_b_diamond_box (pp_b_view s P)"
    unfolding pp_b_diamond_box_def
    using diamond box by simp
qed

lemma pp_b_settles_equivariant:
  "pp_b_equivariant pp_b_settles"
proof (unfold pp_b_equivariant_def, intro allI)
  fix s P
  have db:
      "pp_b_view s (pp_b_diamond (pp_b_box P)) =
        pp_b_diamond (pp_b_box (pp_b_view s P))"
    using pp_b_diamond_box_equivariant
    unfolding pp_b_equivariant_def pp_b_diamond_box_def by blast
  have db_neg:
      "pp_b_view s (pp_b_diamond (pp_b_box (- P))) =
        pp_b_diamond (pp_b_box (- pp_b_view s P))"
  proof -
    have step:
        "pp_b_view s (pp_b_diamond (pp_b_box (- P))) =
          pp_b_diamond (pp_b_box (pp_b_view s (- P)))"
      using pp_b_diamond_box_equivariant
      unfolding pp_b_equivariant_def pp_b_diamond_box_def by blast
    show ?thesis
      using step pp_b_view_complement by simp
  qed
  show "pp_b_view s (pp_b_settles P) =
      pp_b_settles (pp_b_view s P)"
    unfolding pp_b_settles_def pp_b_view_union
    using db db_neg by simp
qed

lemma pp_t_zf_of_b_eqv_true_iff:
  "pp_t_eqv Prop w (pp_zf_of_b P) (pp_zf_truth True)
    \<longleftrightarrow> w \<in> pp_b_box P"
  unfolding pp_t_eqv.simps pp_zf_of_b_def
    pp_b_box_def prefix_def
  by auto

lemma pp_t_zf_of_b_eqv_false_iff:
  "pp_t_eqv Prop w (pp_zf_of_b P) (pp_zf_truth False)
    \<longleftrightarrow> w \<in> pp_b_box (- P)"
  unfolding pp_t_eqv.simps pp_zf_of_b_def
    pp_b_box_def prefix_def
  by auto

lemma pp_t_future_not_mem_iff:
  "(\<exists>v. prefix w v \<and> v \<notin> P) \<longleftrightarrow>
    (\<exists>u. w @ u \<notin> P)"
  by (auto simp: prefix_def)

lemma pp_t_future_box_iff:
  "(\<exists>v. prefix w v \<and> v \<in> pp_b_box P)
    \<longleftrightarrow> w \<in> pp_b_diamond_box P"
proof
  assume "\<exists>v. prefix w v \<and> v \<in> pp_b_box P"
  then obtain v u where
      v: "v = w @ u"
      and box: "v \<in> pp_b_box P"
    by (auto simp: prefix_def)
  show "w \<in> pp_b_diamond_box P"
    using box
    unfolding pp_b_diamond_box_def pp_b_diamond_def
    by (intro CollectI exI[of _ u]) (simp add: v)
next
  assume "w \<in> pp_b_diamond_box P"
  then obtain u where box: "w @ u \<in> pp_b_box P"
    unfolding pp_b_diamond_box_def pp_b_diamond_def by blast
  show "\<exists>v. prefix w v \<and> v \<in> pp_b_box P"
    using box
    by (intro exI[of _ "w @ u"]) (simp add: prefix_def)
qed

lemma pp_b_operator_of_not_box:
  "pp_b_operator_of pp_t_not_box_classifier = pp_b_not_box"
proof (rule ext, rule set_eqI)
  fix P w
  have q: "Elem (pp_zf_of_b P) (pp_t_domain Prop)"
    by (rule pp_zf_of_b_in_domain)
  show "w \<in> pp_b_operator_of pp_t_not_box_classifier P
      \<longleftrightarrow> w \<in> pp_b_not_box P"
    using pp_t_not_box_classifier_holds[OF q, of w]
    unfolding pp_b_operator_of_def pp_b_of_zf_def
      pp_b_not_box_def pp_b_box_def
    by (simp add: pp_t_zf_of_b_eqv_true_iff
        pp_t_future_not_mem_iff)
qed

lemma pp_b_operator_of_diamond_box:
  "pp_b_operator_of pp_t_diamond_box_classifier =
    pp_b_diamond_box"
proof (rule ext, rule set_eqI)
  fix P w
  have q: "Elem (pp_zf_of_b P) (pp_t_domain Prop)"
    by (rule pp_zf_of_b_in_domain)
  have semantics:
      "pp_t_holds
          (pp_t_diamond_box_classifier \<acute> pp_zf_of_b P) w
        \<longleftrightarrow>
        (\<exists>v. prefix w v \<and>
          pp_t_eqv Prop v (pp_zf_of_b P)
            (pp_zf_truth True))"
    using pp_t_diamond_box_classifier_holds[OF q, of w] .
  have abstract:
      "(\<exists>v. prefix w v \<and>
          pp_t_eqv Prop v (pp_zf_of_b P)
            (pp_zf_truth True))
        \<longleftrightarrow> w \<in> pp_b_diamond_box P"
    using pp_t_future_box_iff[of w P]
    by (simp only: pp_t_zf_of_b_eqv_true_iff)
  show "w \<in> pp_b_operator_of pp_t_diamond_box_classifier P
      \<longleftrightarrow> w \<in> pp_b_diamond_box P"
    unfolding pp_b_operator_of_def pp_b_of_zf_def
    using semantics abstract by blast
qed

lemma pp_b_operator_of_settles:
  "pp_b_operator_of (pp_t_closed_den pp_t_settles_operator) =
    pp_b_settles"
proof (rule ext, rule set_eqI)
  fix P w
  have q: "Elem (pp_zf_of_b P) (pp_t_domain Prop)"
    by (rule pp_zf_of_b_in_domain)
  have semantics:
      "pp_t_holds
          ((pp_t_closed_den pp_t_settles_operator) \<acute>
            pp_zf_of_b P) w
        \<longleftrightarrow>
        ((\<exists>v. prefix w v \<and>
            pp_t_eqv Prop v (pp_zf_of_b P)
              (pp_zf_truth True)) \<or>
         (\<exists>v. prefix w v \<and>
            pp_t_eqv Prop v (pp_zf_of_b P)
              (pp_zf_truth False)))"
    using pp_t_settles_den_holds[OF q, of w] .
  have true_branch:
      "(\<exists>v. prefix w v \<and>
          pp_t_eqv Prop v (pp_zf_of_b P)
            (pp_zf_truth True))
        \<longleftrightarrow> w \<in> pp_b_diamond_box P"
    using pp_t_future_box_iff[of w P]
    by (simp only: pp_t_zf_of_b_eqv_true_iff)
  have false_branch:
      "(\<exists>v. prefix w v \<and>
          pp_t_eqv Prop v (pp_zf_of_b P)
            (pp_zf_truth False))
        \<longleftrightarrow> w \<in> pp_b_diamond_box (- P)"
    using pp_t_future_box_iff[of w "- P"]
    by (simp only: pp_t_zf_of_b_eqv_false_iff)
  show "w \<in>
      pp_b_operator_of (pp_t_closed_den pp_t_settles_operator) P
      \<longleftrightarrow> w \<in> pp_b_settles P"
    unfolding pp_b_operator_of_def pp_b_of_zf_def
      pp_b_settles_def
    using semantics true_branch false_branch
    by (simp add: pp_b_diamond_box_def)
qed

lemma pp_b_operator_of_not_box_equivariant:
  "pp_b_equivariant (pp_b_operator_of pp_t_not_box_classifier)"
  unfolding pp_b_operator_of_not_box
  by (rule pp_b_not_box_equivariant)

lemma pp_b_operator_of_diamond_box_equivariant:
  "pp_b_equivariant
    (pp_b_operator_of pp_t_diamond_box_classifier)"
  unfolding pp_b_operator_of_diamond_box
  by (rule pp_b_diamond_box_equivariant)

lemma pp_b_operator_of_settles_equivariant:
  "pp_b_equivariant
    (pp_b_operator_of
      (pp_t_closed_den pp_t_settles_operator))"
  unfolding pp_b_operator_of_settles
  by (rule pp_b_settles_equivariant)

definition pp_t_known_obstruction_operators :: "ZF set" where
  "pp_t_known_obstruction_operators =
    {pp_t_not_box_classifier,
     pp_t_diamond_box_classifier,
     pp_t_closed_den pp_t_settles_operator}"

lemma pp_t_known_obstruction_operators_equivariant:
  assumes "X \<in> pp_t_known_obstruction_operators"
  shows "pp_b_equivariant (pp_b_operator_of X)"
  using assms pp_b_operator_of_not_box_equivariant
    pp_b_operator_of_diamond_box_equivariant
    pp_b_operator_of_settles_equivariant
  unfolding pp_t_known_obstruction_operators_def
  by auto

theorem pp_t_generic_seed_for_known_obstructions:
  "\<exists>r. Elem r (pp_t_domain Prop) \<and>
    (\<forall>X \<in> pp_t_known_obstruction_operators.
      ((\<forall>w. pp_t_holds (X \<acute> r) w) \<longrightarrow>
       (\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
          pp_t_holds (X \<acute> q) [])))"
proof -
  let ?Stock =
    "pp_b_operator_of ` pp_t_known_obstruction_operators"
  have countable: "countable ?Stock"
    by (simp add: pp_t_known_obstruction_operators_def)
  have equivariant:
      "\<And>F. F \<in> ?Stock \<Longrightarrow> pp_b_equivariant F"
    using pp_t_known_obstruction_operators_equivariant by blast
  obtain R where generic:
      "\<forall>F \<in> ?Stock.
        pp_b_root_unary_recombination F R"
    using pp_b_generic_witness_for_countable_stock[
      OF countable equivariant] by blast
  let ?r = "pp_zf_of_b R"
  show ?thesis
  proof (intro exI[of _ ?r] conjI ballI impI)
    show "Elem ?r (pp_t_domain Prop)"
      by (rule pp_zf_of_b_in_domain)
  next
    fix X
    assume X: "X \<in> pp_t_known_obstruction_operators"
      and necessary: "\<forall>w. pp_t_holds (X \<acute> ?r) w"
    have mapped: "pp_b_operator_of X \<in> ?Stock"
      using X by blast
    have recombines:
        "pp_b_root_unary_recombination
          (pp_b_operator_of X) R"
      using generic mapped by blast
    show "\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
        pp_t_holds (X \<acute> q) []"
      using pp_b_recombination_transfers_to_zf[
        OF recombines necessary] .
  qed
qed

section \<open>The all-type cone relation\<close>

text \<open>
  The remaining bridge is parametricity under the isomorphism between the
  whole Boolean tree and any cone below a word \<open>s\<close>.  At proposition type,
  the relation says exactly that the right proposition is the view of the
  left proposition from \<open>s\<close>.  The arrow clause is the usual logical
  relation.  Its two-sided totality is what is needed to reindex higher-order
  quantifiers.
\<close>

fun pp_t_cone_rel ::
    "otype \<Rightarrow> bool list \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> bool"
where
  "pp_t_cone_rel Ind s x y = (x = y)"
| "pp_t_cone_rel Prop s P Q =
    (\<forall>u. pp_t_holds P (s @ u) \<longleftrightarrow> pp_t_holds Q u)"
| "pp_t_cone_rel (\<sigma> \<rightarrow>\<^sub>o \<tau>) s f g =
    (\<forall>x y.
      Elem x (pp_t_domain \<sigma>) \<longrightarrow>
      Elem y (pp_t_domain \<sigma>) \<longrightarrow>
      pp_t_cone_rel \<sigma> s x y \<longrightarrow>
      pp_t_cone_rel \<tau> s (f \<acute> x) (g \<acute> y))"

definition pp_t_cone_left_total ::
    "otype \<Rightarrow> bool list \<Rightarrow> bool"
where
  "pp_t_cone_left_total \<sigma> s \<longleftrightarrow>
    (\<forall>x. Elem x (pp_t_domain \<sigma>) \<longrightarrow>
      (\<exists>y. Elem y (pp_t_domain \<sigma>) \<and>
        pp_t_cone_rel \<sigma> s x y))"

definition pp_t_cone_right_total ::
    "otype \<Rightarrow> bool list \<Rightarrow> bool"
where
  "pp_t_cone_right_total \<sigma> s \<longleftrightarrow>
    (\<forall>y. Elem y (pp_t_domain \<sigma>) \<longrightarrow>
      (\<exists>x. Elem x (pp_t_domain \<sigma>) \<and>
        pp_t_cone_rel \<sigma> s x y))"

definition pp_t_cone_view :: "bool list \<Rightarrow> ZF \<Rightarrow> ZF" where
  "pp_t_cone_view s P =
    pp_zf_of_b (pp_b_view s (pp_b_of_zf P))"

definition pp_t_cone_lift :: "bool list \<Rightarrow> ZF \<Rightarrow> ZF" where
  "pp_t_cone_lift s Q =
    pp_zf_of_b (pp_b_lift s (pp_b_of_zf Q))"

lemma pp_t_cone_view_in_domain:
  "Elem (pp_t_cone_view s P) (pp_t_domain Prop)"
  unfolding pp_t_cone_view_def
  by (rule pp_zf_of_b_in_domain)

lemma pp_t_cone_lift_in_domain:
  "Elem (pp_t_cone_lift s Q) (pp_t_domain Prop)"
  unfolding pp_t_cone_lift_def
  by (rule pp_zf_of_b_in_domain)

lemma pp_t_cone_view_holds[simp]:
  "pp_t_holds (pp_t_cone_view s P) u
    \<longleftrightarrow> pp_t_holds P (s @ u)"
  by (simp add: pp_t_cone_view_def pp_b_view_def
      pp_b_of_zf_def)

lemma pp_t_cone_lift_holds:
  "pp_t_holds (pp_t_cone_lift s Q) v
    \<longleftrightarrow>
    (\<exists>u. v = s @ u \<and> pp_t_holds Q u)"
  by (auto simp: pp_t_cone_lift_def pp_b_lift_def
      pp_b_of_zf_def)

lemma pp_t_cone_view_preserves_eqv:
  assumes PQ: "pp_t_eqv Prop (s @ t) P Q"
  shows "pp_t_eqv Prop t
    (pp_t_cone_view s P) (pp_t_cone_view s Q)"
  using PQ
  by (auto simp: prefix_def append_assoc)

lemma pp_t_cone_lift_view_eqv:
  assumes P: "Elem P (pp_t_domain Prop)"
  shows "pp_t_eqv Prop s
    (pp_t_cone_lift s (pp_t_cone_view s P)) P"
  by (auto simp: prefix_def pp_t_cone_lift_holds)

lemma pp_t_cone_lift_preserves_eqv:
  assumes QR: "pp_t_eqv Prop w Q R"
  shows "pp_t_eqv Prop (s @ w)
    (pp_t_cone_lift s Q) (pp_t_cone_lift s R)"
  using QR
  by (auto simp: prefix_def pp_t_cone_lift_holds
      append_assoc)

definition pp_t_cone_compatible ::
    "otype \<Rightarrow> bool list \<Rightarrow> bool"
where
  "pp_t_cone_compatible \<sigma> s \<longleftrightarrow>
    (\<forall>u x y x' y'.
      Elem x (pp_t_domain \<sigma>) \<longrightarrow>
      Elem y (pp_t_domain \<sigma>) \<longrightarrow>
      Elem x' (pp_t_domain \<sigma>) \<longrightarrow>
      Elem y' (pp_t_domain \<sigma>) \<longrightarrow>
      pp_t_cone_rel \<sigma> s x y \<longrightarrow>
      pp_t_cone_rel \<sigma> s x' y' \<longrightarrow>
      (pp_t_eqv \<sigma> (s @ u) x x'
        \<longleftrightarrow> pp_t_eqv \<sigma> u y y'))"

definition pp_t_cone_env_rel ::
    "ctx \<Rightarrow> bool list \<Rightarrow> (nat \<Rightarrow> ZF) \<Rightarrow>
      (nat \<Rightarrow> ZF) \<Rightarrow> bool"
where
  "pp_t_cone_env_rel \<Gamma> s \<rho> \<eta> \<longleftrightarrow>
    pp_t_env_typed \<Gamma> \<rho> \<and>
    pp_t_env_typed \<Gamma> \<eta> \<and>
    (\<forall>n \<sigma>. lookup \<Gamma> n = Some \<sigma> \<longrightarrow>
      pp_t_cone_rel \<sigma> s (\<rho> n) (\<eta> n))"

lemma pp_t_cone_env_rel_typed_left:
  "pp_t_cone_env_rel \<Gamma> s \<rho> \<eta> \<Longrightarrow>
    pp_t_env_typed \<Gamma> \<rho>"
  unfolding pp_t_cone_env_rel_def by blast

lemma pp_t_cone_env_rel_typed_right:
  "pp_t_cone_env_rel \<Gamma> s \<rho> \<eta> \<Longrightarrow>
    pp_t_env_typed \<Gamma> \<eta>"
  unfolding pp_t_cone_env_rel_def by blast

lemma pp_t_cone_env_rel_lookup:
  assumes env: "pp_t_cone_env_rel \<Gamma> s \<rho> \<eta>"
    and lookup: "lookup \<Gamma> n = Some \<sigma>"
  shows "pp_t_cone_rel \<sigma> s (\<rho> n) (\<eta> n)"
  using env lookup unfolding pp_t_cone_env_rel_def by blast

lemma pp_t_cone_env_rel_extend:
  assumes env: "pp_t_cone_env_rel \<Gamma> s \<rho> \<eta>"
    and x: "Elem x (pp_t_domain \<sigma>)"
    and y: "Elem y (pp_t_domain \<sigma>)"
    and xy: "pp_t_cone_rel \<sigma> s x y"
  shows "pp_t_cone_env_rel (\<sigma> # \<Gamma>) s
    (extend_env x \<rho>) (extend_env y \<eta>)"
proof (unfold pp_t_cone_env_rel_def, intro conjI allI impI)
  show "pp_t_env_typed (\<sigma> # \<Gamma>) (extend_env x \<rho>)"
    using pp_t_env_typed_extend[
      OF pp_t_cone_env_rel_typed_left[OF env] x] .
  show "pp_t_env_typed (\<sigma> # \<Gamma>) (extend_env y \<eta>)"
    using pp_t_env_typed_extend[
      OF pp_t_cone_env_rel_typed_right[OF env] y] .
  fix n \<tau>
  assume lookup: "lookup (\<sigma> # \<Gamma>) n = Some \<tau>"
  show "pp_t_cone_rel \<tau> s
      (extend_env x \<rho> n) (extend_env y \<eta> n)"
  proof (cases n)
    case 0
    then have "\<tau> = \<sigma>"
      using lookup by simp
    then show ?thesis
      using 0 xy by simp
  next
    case (Suc m)
    then have old_lookup: "lookup \<Gamma> m = Some \<tau>"
      using lookup by simp
    have old_rel: "pp_t_cone_rel \<tau> s (\<rho> m) (\<eta> m)"
      using pp_t_cone_env_rel_lookup[OF env old_lookup] .
    show ?thesis
      using Suc old_rel by simp
  qed
qed

lemma pp_t_cone_rel_prop_view:
  "pp_t_cone_rel Prop s P
    (pp_zf_of_b (pp_b_view s (pp_b_of_zf P)))"
  by (simp add: pp_b_view_def pp_b_of_zf_def)

lemma pp_t_cone_rel_prop_lift:
  "pp_t_cone_rel Prop s
    (pp_zf_of_b (pp_b_lift s (pp_b_of_zf Q))) Q"
proof -
  have view:
      "pp_b_view s
        (pp_b_lift s (pp_b_of_zf Q)) = pp_b_of_zf Q"
    by (rule pp_b_view_lift)
  show ?thesis
    using view
    by (auto simp: pp_t_cone_rel.simps pp_b_view_def
        pp_b_of_zf_def)
qed

lemma pp_t_cone_left_total_Ind:
  "pp_t_cone_left_total Ind s"
  unfolding pp_t_cone_left_total_def
  by auto

lemma pp_t_cone_right_total_Ind:
  "pp_t_cone_right_total Ind s"
  unfolding pp_t_cone_right_total_def
  by auto

lemma pp_t_cone_left_total_Prop:
  "pp_t_cone_left_total Prop s"
proof (unfold pp_t_cone_left_total_def, intro allI impI)
  fix P
  assume P: "Elem P (pp_t_domain Prop)"
  let ?Q = "pp_zf_of_b (pp_b_view s (pp_b_of_zf P))"
  show "\<exists>Q. Elem Q (pp_t_domain Prop) \<and>
      pp_t_cone_rel Prop s P Q"
    using pp_zf_of_b_in_domain pp_t_cone_rel_prop_view
    by (intro exI[of _ ?Q]) blast
qed

lemma pp_t_cone_right_total_Prop:
  "pp_t_cone_right_total Prop s"
proof (unfold pp_t_cone_right_total_def, intro allI impI)
  fix Q
  assume Q: "Elem Q (pp_t_domain Prop)"
  let ?P = "pp_zf_of_b (pp_b_lift s (pp_b_of_zf Q))"
  show "\<exists>P. Elem P (pp_t_domain Prop) \<and>
      pp_t_cone_rel Prop s P Q"
    using pp_zf_of_b_in_domain pp_t_cone_rel_prop_lift
    by (intro exI[of _ ?P]) blast
qed

definition pp_t_cone_push ::
    "otype \<Rightarrow> bool list \<Rightarrow> ZF \<Rightarrow> ZF"
where
  "pp_t_cone_push \<sigma> s x =
    (SOME y. Elem y (pp_t_domain \<sigma>) \<and>
      pp_t_cone_rel \<sigma> s x y)"

definition pp_t_cone_pull ::
    "otype \<Rightarrow> bool list \<Rightarrow> ZF \<Rightarrow> ZF"
where
  "pp_t_cone_pull \<sigma> s y =
    (SOME x. Elem x (pp_t_domain \<sigma>) \<and>
      pp_t_cone_rel \<sigma> s x y)"

lemma pp_t_cone_push_spec:
  assumes total: "pp_t_cone_left_total \<sigma> s"
    and x: "Elem x (pp_t_domain \<sigma>)"
  shows "Elem (pp_t_cone_push \<sigma> s x) (pp_t_domain \<sigma>)"
    and "pp_t_cone_rel \<sigma> s x (pp_t_cone_push \<sigma> s x)"
proof -
  have exists:
      "\<exists>y. Elem y (pp_t_domain \<sigma>) \<and>
        pp_t_cone_rel \<sigma> s x y"
    using total x unfolding pp_t_cone_left_total_def by blast
  have chosen:
      "Elem (pp_t_cone_push \<sigma> s x) (pp_t_domain \<sigma>) \<and>
        pp_t_cone_rel \<sigma> s x (pp_t_cone_push \<sigma> s x)"
    unfolding pp_t_cone_push_def
    using someI_ex[OF exists] .
  then show
    "Elem (pp_t_cone_push \<sigma> s x) (pp_t_domain \<sigma>)"
    "pp_t_cone_rel \<sigma> s x (pp_t_cone_push \<sigma> s x)"
    by blast+
qed

lemma pp_t_cone_pull_spec:
  assumes total: "pp_t_cone_right_total \<sigma> s"
    and y: "Elem y (pp_t_domain \<sigma>)"
  shows "Elem (pp_t_cone_pull \<sigma> s y) (pp_t_domain \<sigma>)"
    and "pp_t_cone_rel \<sigma> s
      (pp_t_cone_pull \<sigma> s y) y"
proof -
  have exists:
      "\<exists>x. Elem x (pp_t_domain \<sigma>) \<and>
        pp_t_cone_rel \<sigma> s x y"
    using total y unfolding pp_t_cone_right_total_def by blast
  have chosen:
      "Elem (pp_t_cone_pull \<sigma> s y) (pp_t_domain \<sigma>) \<and>
        pp_t_cone_rel \<sigma> s (pp_t_cone_pull \<sigma> s y) y"
    unfolding pp_t_cone_pull_def
    using someI_ex[OF exists] .
  then show
    "Elem (pp_t_cone_pull \<sigma> s y) (pp_t_domain \<sigma>)"
    "pp_t_cone_rel \<sigma> s (pp_t_cone_pull \<sigma> s y) y"
    by blast+
qed

lemma pp_t_cone_rel_replace_left:
  assumes x: "Elem x (pp_t_domain \<sigma>)"
    and x': "Elem x' (pp_t_domain \<sigma>)"
    and y: "Elem y (pp_t_domain \<sigma>)"
    and xy: "pp_t_cone_rel \<sigma> s x y"
    and x'x: "pp_t_eqv \<sigma> s x' x"
  shows "pp_t_cone_rel \<sigma> s x' y"
  using assms
proof (induction \<sigma> arbitrary: s x x' y)
  case Ind
  then show ?case by simp
next
  case Prop
  then show ?case
    by (auto simp: prefix_def)
next
  case (Arr \<sigma> \<tau>)
  show ?case
    unfolding pp_t_cone_rel.simps
  proof (intro allI impI)
    fix a b
    assume a: "Elem a (pp_t_domain \<sigma>)"
      and b: "Elem b (pp_t_domain \<sigma>)"
      and ab: "pp_t_cone_rel \<sigma> s a b"
    have aa: "pp_t_eqv \<sigma> s a a"
      using pp_t_eqv_reflexive[OF a] .
    have output_eqv:
        "pp_t_eqv \<tau> s (x' \<acute> a) (x \<acute> a)"
      using Arr.prems(5) a a aa by auto
    have output_rel:
        "pp_t_cone_rel \<tau> s (x \<acute> a) (y \<acute> b)"
      using Arr.prems(4) a b ab by auto
    have x'a: "Elem (x' \<acute> a) (pp_t_domain \<tau>)"
      using pp_t_app_closed[OF Arr.prems(2) a] .
    have xa: "Elem (x \<acute> a) (pp_t_domain \<tau>)"
      using pp_t_app_closed[OF Arr.prems(1) a] .
    have yb: "Elem (y \<acute> b) (pp_t_domain \<tau>)"
      using pp_t_app_closed[OF Arr.prems(3) b] .
    show "pp_t_cone_rel \<tau> s (x' \<acute> a) (y \<acute> b)"
      using Arr.IH(2)[OF xa x'a yb output_rel output_eqv] .
  qed
qed

lemma pp_t_cone_rel_replace_right:
  assumes x: "Elem x (pp_t_domain \<sigma>)"
    and y: "Elem y (pp_t_domain \<sigma>)"
    and y': "Elem y' (pp_t_domain \<sigma>)"
    and xy: "pp_t_cone_rel \<sigma> s x y"
    and y'y: "pp_t_eqv \<sigma> [] y' y"
  shows "pp_t_cone_rel \<sigma> s x y'"
  using assms
proof (induction \<sigma> arbitrary: s x y y')
  case Ind
  then show ?case by simp
next
  case Prop
  then show ?case
    by auto
next
  case (Arr \<sigma> \<tau>)
  show ?case
    unfolding pp_t_cone_rel.simps
  proof (intro allI impI)
    fix a b
    assume a: "Elem a (pp_t_domain \<sigma>)"
      and b: "Elem b (pp_t_domain \<sigma>)"
      and ab: "pp_t_cone_rel \<sigma> s a b"
    have bb: "pp_t_eqv \<sigma> [] b b"
      using pp_t_eqv_reflexive[OF b] .
    have output_eqv:
        "pp_t_eqv \<tau> [] (y' \<acute> b) (y \<acute> b)"
      using Arr.prems(5) b b bb by auto
    have output_rel:
        "pp_t_cone_rel \<tau> s (x \<acute> a) (y \<acute> b)"
      using Arr.prems(4) a b ab by auto
    have xa: "Elem (x \<acute> a) (pp_t_domain \<tau>)"
      using pp_t_app_closed[OF Arr.prems(1) a] .
    have yb: "Elem (y \<acute> b) (pp_t_domain \<tau>)"
      using pp_t_app_closed[OF Arr.prems(2) b] .
    have y'b: "Elem (y' \<acute> b) (pp_t_domain \<tau>)"
      using pp_t_app_closed[OF Arr.prems(3) b] .
    show "pp_t_cone_rel \<tau> s (x \<acute> a) (y' \<acute> b)"
      using Arr.IH(2)[OF xa yb y'b output_rel output_eqv] .
  qed
qed

lemma pp_t_cone_compatible_Ind:
  "pp_t_cone_compatible Ind s"
  unfolding pp_t_cone_compatible_def
  by auto

lemma pp_t_cone_compatible_Prop:
  "pp_t_cone_compatible Prop s"
  unfolding pp_t_cone_compatible_def
  by (auto simp: prefix_def append_assoc)

lemma pp_t_cone_compatible_Arr:
  assumes left: "pp_t_cone_left_total \<sigma> s"
    and right: "pp_t_cone_right_total \<sigma> s"
    and arg_compatible: "pp_t_cone_compatible \<sigma> s"
    and target_compatible: "pp_t_cone_compatible \<tau> s"
  shows "pp_t_cone_compatible (\<sigma> \<rightarrow>\<^sub>o \<tau>) s"
  unfolding pp_t_cone_compatible_def
proof (intro allI impI)
  fix u f g f' g'
  assume f: "Elem f (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    and g: "Elem g (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    and f': "Elem f' (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    and g': "Elem g' (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    and fg: "pp_t_cone_rel (\<sigma> \<rightarrow>\<^sub>o \<tau>) s f g"
    and f'g': "pp_t_cone_rel (\<sigma> \<rightarrow>\<^sub>o \<tau>) s f' g'"
  show "pp_t_eqv (\<sigma> \<rightarrow>\<^sub>o \<tau>) (s @ u) f f'
    \<longleftrightarrow> pp_t_eqv (\<sigma> \<rightarrow>\<^sub>o \<tau>) u g g'"
  proof
    assume left_eqv:
        "pp_t_eqv (\<sigma> \<rightarrow>\<^sub>o \<tau>) (s @ u) f f'"
    show "pp_t_eqv (\<sigma> \<rightarrow>\<^sub>o \<tau>) u g g'"
      unfolding pp_t_eqv.simps
    proof (intro allI impI)
      fix v b b'
      assume future: "prefix u v"
        and b: "Elem b (pp_t_domain \<sigma>)"
        and b': "Elem b' (pp_t_domain \<sigma>)"
        and bb': "pp_t_eqv \<sigma> v b b'"
      obtain a where a: "Elem a (pp_t_domain \<sigma>)"
        and ab: "pp_t_cone_rel \<sigma> s a b"
        using right b unfolding pp_t_cone_right_total_def by blast
      obtain a' where a': "Elem a' (pp_t_domain \<sigma>)"
        and a'b': "pp_t_cone_rel \<sigma> s a' b'"
        using right b' unfolding pp_t_cone_right_total_def by blast
      have aa': "pp_t_eqv \<sigma> (s @ v) a a'"
        using arg_compatible a b a' b' ab a'b' bb'
        unfolding pp_t_cone_compatible_def by blast
      have cone_future: "prefix (s @ u) (s @ v)"
        using future by (auto simp: prefix_def append_assoc)
      have left_outputs:
          "pp_t_eqv \<tau> (s @ v) (f \<acute> a) (f' \<acute> a')"
        using left_eqv cone_future a a' aa' by auto
      have fb: "pp_t_cone_rel \<tau> s (f \<acute> a) (g \<acute> b)"
        using fg a b ab by auto
      have f'b':
          "pp_t_cone_rel \<tau> s (f' \<acute> a') (g' \<acute> b')"
        using f'g' a' b' a'b' by auto
      have fa: "Elem (f \<acute> a) (pp_t_domain \<tau>)"
        using pp_t_app_closed[OF f a] .
      have gb: "Elem (g \<acute> b) (pp_t_domain \<tau>)"
        using pp_t_app_closed[OF g b] .
      have f'a': "Elem (f' \<acute> a') (pp_t_domain \<tau>)"
        using pp_t_app_closed[OF f' a'] .
      have g'b': "Elem (g' \<acute> b') (pp_t_domain \<tau>)"
        using pp_t_app_closed[OF g' b'] .
      show "pp_t_eqv \<tau> v (g \<acute> b) (g' \<acute> b')"
        using target_compatible fa gb f'a' g'b' fb f'b'
          left_outputs
        unfolding pp_t_cone_compatible_def by blast
    qed
  next
    assume right_eqv:
        "pp_t_eqv (\<sigma> \<rightarrow>\<^sub>o \<tau>) u g g'"
    show "pp_t_eqv (\<sigma> \<rightarrow>\<^sub>o \<tau>) (s @ u) f f'"
      unfolding pp_t_eqv.simps
    proof (intro allI impI)
      fix z a a'
      assume future: "prefix (s @ u) z"
        and a: "Elem a (pp_t_domain \<sigma>)"
        and a': "Elem a' (pp_t_domain \<sigma>)"
        and aa': "pp_t_eqv \<sigma> z a a'"
      obtain v where z: "z = s @ v" and uv: "prefix u v"
        using future by (auto simp: prefix_def append_assoc)
      obtain b where b: "Elem b (pp_t_domain \<sigma>)"
        and ab: "pp_t_cone_rel \<sigma> s a b"
        using left a unfolding pp_t_cone_left_total_def by blast
      obtain b' where b': "Elem b' (pp_t_domain \<sigma>)"
        and a'b': "pp_t_cone_rel \<sigma> s a' b'"
        using left a' unfolding pp_t_cone_left_total_def by blast
      have bb': "pp_t_eqv \<sigma> v b b'"
        using arg_compatible a b a' b' ab a'b' aa' z
        unfolding pp_t_cone_compatible_def by blast
      have right_outputs:
          "pp_t_eqv \<tau> v (g \<acute> b) (g' \<acute> b')"
        using right_eqv uv b b' bb' by auto
      have fb: "pp_t_cone_rel \<tau> s (f \<acute> a) (g \<acute> b)"
        using fg a b ab by auto
      have f'b':
          "pp_t_cone_rel \<tau> s (f' \<acute> a') (g' \<acute> b')"
        using f'g' a' b' a'b' by auto
      have fa: "Elem (f \<acute> a) (pp_t_domain \<tau>)"
        using pp_t_app_closed[OF f a] .
      have gb: "Elem (g \<acute> b) (pp_t_domain \<tau>)"
        using pp_t_app_closed[OF g b] .
      have f'a': "Elem (f' \<acute> a') (pp_t_domain \<tau>)"
        using pp_t_app_closed[OF f' a'] .
      have g'b': "Elem (g' \<acute> b') (pp_t_domain \<tau>)"
        using pp_t_app_closed[OF g' b'] .
      show "pp_t_eqv \<tau> z (f \<acute> a) (f' \<acute> a')"
        using target_compatible fa gb f'a' g'b' fb f'b'
          right_outputs z
        unfolding pp_t_cone_compatible_def by blast
    qed
  qed
qed

lemma pp_t_cone_left_total_Arr:
  assumes arg_right: "pp_t_cone_right_total \<sigma> s"
    and target_left: "pp_t_cone_left_total \<tau> s"
    and arg_compatible: "pp_t_cone_compatible \<sigma> s"
    and target_compatible: "pp_t_cone_compatible \<tau> s"
  shows "pp_t_cone_left_total (\<sigma> \<rightarrow>\<^sub>o \<tau>) s"
proof (unfold pp_t_cone_left_total_def, intro allI impI)
  fix f
  assume f: "Elem f (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
  let ?g =
    "Lambda (pp_t_domain \<sigma>)
      (\<lambda>y. pp_t_cone_push \<tau> s
        (f \<acute> pp_t_cone_pull \<sigma> s y))"
  have g_domain:
      "Elem ?g (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
  proof (rule pp_t_lambda_closed)
    fix y
    assume y: "Elem y (pp_t_domain \<sigma>)"
    have pull:
        "Elem (pp_t_cone_pull \<sigma> s y) (pp_t_domain \<sigma>)"
      using pp_t_cone_pull_spec(1)[OF arg_right y] .
    have image:
        "Elem (f \<acute> pp_t_cone_pull \<sigma> s y)
          (pp_t_domain \<tau>)"
      using pp_t_app_closed[OF f pull] .
    show "Elem
        (pp_t_cone_push \<tau> s
          (f \<acute> pp_t_cone_pull \<sigma> s y))
        (pp_t_domain \<tau>)"
      using pp_t_cone_push_spec(1)[OF target_left image] .
  next
    fix w y y'
    assume y: "Elem y (pp_t_domain \<sigma>)"
      and y': "Elem y' (pp_t_domain \<sigma>)"
      and yy': "pp_t_eqv \<sigma> w y y'"
    let ?x = "pp_t_cone_pull \<sigma> s y"
    let ?x' = "pp_t_cone_pull \<sigma> s y'"
    let ?z = "pp_t_cone_push \<tau> s (f \<acute> ?x)"
    let ?z' = "pp_t_cone_push \<tau> s (f \<acute> ?x')"
    have x: "Elem ?x (pp_t_domain \<sigma>)"
      using pp_t_cone_pull_spec(1)[OF arg_right y] .
    have x': "Elem ?x' (pp_t_domain \<sigma>)"
      using pp_t_cone_pull_spec(1)[OF arg_right y'] .
    have xy: "pp_t_cone_rel \<sigma> s ?x y"
      using pp_t_cone_pull_spec(2)[OF arg_right y] .
    have x'y': "pp_t_cone_rel \<sigma> s ?x' y'"
      using pp_t_cone_pull_spec(2)[OF arg_right y'] .
    have xx': "pp_t_eqv \<sigma> (s @ w) ?x ?x'"
      using arg_compatible x y x' y' xy x'y' yy'
      unfolding pp_t_cone_compatible_def by blast
    have fx: "Elem (f \<acute> ?x) (pp_t_domain \<tau>)"
      using pp_t_app_closed[OF f x] .
    have fx': "Elem (f \<acute> ?x') (pp_t_domain \<tau>)"
      using pp_t_app_closed[OF f x'] .
    have images:
        "pp_t_eqv \<tau> (s @ w) (f \<acute> ?x) (f \<acute> ?x')"
      using pp_t_arrow_member_respects[OF f x x' xx'] .
    have z: "Elem ?z (pp_t_domain \<tau>)"
      using pp_t_cone_push_spec(1)[OF target_left fx] .
    have z': "Elem ?z' (pp_t_domain \<tau>)"
      using pp_t_cone_push_spec(1)[OF target_left fx'] .
    have fxz: "pp_t_cone_rel \<tau> s (f \<acute> ?x) ?z"
      using pp_t_cone_push_spec(2)[OF target_left fx] .
    have fx'z': "pp_t_cone_rel \<tau> s (f \<acute> ?x') ?z'"
      using pp_t_cone_push_spec(2)[OF target_left fx'] .
    show "pp_t_eqv \<tau> w
        (pp_t_cone_push \<tau> s
          (f \<acute> pp_t_cone_pull \<sigma> s y))
        (pp_t_cone_push \<tau> s
          (f \<acute> pp_t_cone_pull \<sigma> s y'))"
      using target_compatible fx z fx' z' fxz fx'z' images
      unfolding pp_t_cone_compatible_def by blast
  qed
  have fg:
      "pp_t_cone_rel (\<sigma> \<rightarrow>\<^sub>o \<tau>) s f ?g"
    unfolding pp_t_cone_rel.simps
  proof (intro allI impI)
    fix x y
    assume x: "Elem x (pp_t_domain \<sigma>)"
      and y: "Elem y (pp_t_domain \<sigma>)"
      and xy: "pp_t_cone_rel \<sigma> s x y"
    let ?a = "pp_t_cone_pull \<sigma> s y"
    let ?z = "pp_t_cone_push \<tau> s (f \<acute> ?a)"
    have a: "Elem ?a (pp_t_domain \<sigma>)"
      using pp_t_cone_pull_spec(1)[OF arg_right y] .
    have ay: "pp_t_cone_rel \<sigma> s ?a y"
      using pp_t_cone_pull_spec(2)[OF arg_right y] .
    have yy: "pp_t_eqv \<sigma> [] y y"
      using pp_t_eqv_reflexive[OF y] .
    have xa_iff:
        "pp_t_eqv \<sigma> (s @ []) x ?a
          \<longleftrightarrow> pp_t_eqv \<sigma> [] y y"
      using arg_compatible x y a y xy ay
      unfolding pp_t_cone_compatible_def by blast
    have xa: "pp_t_eqv \<sigma> s x ?a"
      using xa_iff yy by simp
    have fx: "Elem (f \<acute> x) (pp_t_domain \<tau>)"
      using pp_t_app_closed[OF f x] .
    have fa: "Elem (f \<acute> ?a) (pp_t_domain \<tau>)"
      using pp_t_app_closed[OF f a] .
    have fxa: "pp_t_eqv \<tau> s (f \<acute> x) (f \<acute> ?a)"
      using pp_t_arrow_member_respects[OF f x a xa] .
    have z: "Elem ?z (pp_t_domain \<tau>)"
      using pp_t_cone_push_spec(1)[OF target_left fa] .
    have faz: "pp_t_cone_rel \<tau> s (f \<acute> ?a) ?z"
      using pp_t_cone_push_spec(2)[OF target_left fa] .
    have fxz: "pp_t_cone_rel \<tau> s (f \<acute> x) ?z"
      using pp_t_cone_rel_replace_left[
        OF fa fx z faz fxa] .
    show "pp_t_cone_rel \<tau> s (f \<acute> x) (?g \<acute> y)"
      using fxz y by (simp add: Lambda_app)
  qed
  show "\<exists>g. Elem g (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>)) \<and>
      pp_t_cone_rel (\<sigma> \<rightarrow>\<^sub>o \<tau>) s f g"
    using g_domain fg by blast
qed

lemma pp_t_cone_left_total_Prop_Prop:
  "pp_t_cone_left_total (Prop \<rightarrow>\<^sub>o Prop) s"
  by (rule pp_t_cone_left_total_Arr[
    OF pp_t_cone_right_total_Prop pp_t_cone_left_total_Prop
      pp_t_cone_compatible_Prop pp_t_cone_compatible_Prop])

lemma pp_t_cone_compatible_Prop_Prop:
  "pp_t_cone_compatible (Prop \<rightarrow>\<^sub>o Prop) s"
  by (rule pp_t_cone_compatible_Arr[
    OF pp_t_cone_left_total_Prop pp_t_cone_right_total_Prop
      pp_t_cone_compatible_Prop pp_t_cone_compatible_Prop])

lemma pp_t_cone_extended_prop_operator_respects:
  assumes g:
      "Elem g (pp_t_domain (Prop \<rightarrow>\<^sub>o Prop))"
    and P: "Elem P (pp_t_domain Prop)"
    and Q: "Elem Q (pp_t_domain Prop)"
    and PQ: "pp_t_eqv Prop w P Q"
  shows "pp_t_eqv Prop w
    (pp_t_cone_lift s (g \<acute> pp_t_cone_view s P))
    (pp_t_cone_lift s (g \<acute> pp_t_cone_view s Q))"
  unfolding pp_t_eqv.simps
proof (intro allI impI)
  fix v
  assume future: "prefix w v"
  show "pp_t_holds
        (pp_t_cone_lift s (g \<acute> pp_t_cone_view s P)) v
      \<longleftrightarrow>
      pp_t_holds
        (pp_t_cone_lift s (g \<acute> pp_t_cone_view s Q)) v"
  proof (cases "prefix s v")
    case False
    then show ?thesis
      by (auto simp: pp_t_cone_lift_holds prefix_def)
  next
    case True
    then obtain u where v: "v = s @ u"
      by (auto simp: prefix_def)
    have comparable: "prefix w s \<or> prefix s w"
      using prefix_same_cases[OF future True] .
    have output_iff:
        "pp_t_holds (g \<acute> pp_t_cone_view s P) u
          \<longleftrightarrow>
        pp_t_holds (g \<acute> pp_t_cone_view s Q) u"
    proof -
      from comparable show ?thesis
      proof
        assume ws: "prefix w s"
      have PQ_s: "pp_t_eqv Prop s P Q"
          using pp_t_eqv_persistent[OF PQ ws] .
      have views:
          "pp_t_eqv Prop []
            (pp_t_cone_view s P) (pp_t_cone_view s Q)"
        using pp_t_cone_view_preserves_eqv[
          of s "[]" P Q] PQ_s by simp
      have outputs:
          "pp_t_eqv Prop []
            (g \<acute> pp_t_cone_view s P)
            (g \<acute> pp_t_cone_view s Q)"
        using pp_t_arrow_member_respects[
          OF g pp_t_cone_view_in_domain
            pp_t_cone_view_in_domain views] .
      show ?thesis
        using pp_t_prop_eqv_at[OF outputs, of u] by simp
      next
        assume sw: "prefix s w"
        then obtain t where w: "w = s @ t"
        by (auto simp: prefix_def)
      have views:
          "pp_t_eqv Prop t
            (pp_t_cone_view s P) (pp_t_cone_view s Q)"
        using pp_t_cone_view_preserves_eqv[
          of s t P Q] PQ w by simp
      have outputs:
          "pp_t_eqv Prop t
            (g \<acute> pp_t_cone_view s P)
            (g \<acute> pp_t_cone_view s Q)"
        using pp_t_arrow_member_respects[
          OF g pp_t_cone_view_in_domain
            pp_t_cone_view_in_domain views] .
      have tu: "prefix t u"
        using future w v by simp
      show ?thesis
        using pp_t_prop_eqv_at[OF outputs tu] .
      qed
    qed
    show ?thesis
      using output_iff v
      by (simp add: pp_t_cone_lift_holds)
  qed
qed

definition pp_t_cone_extend_prop_operator ::
    "bool list \<Rightarrow> ZF \<Rightarrow> ZF"
where
  "pp_t_cone_extend_prop_operator s g =
    Lambda (pp_t_domain Prop)
      (\<lambda>P. pp_t_cone_lift s
        (g \<acute> pp_t_cone_view s P))"

lemma pp_t_cone_extend_prop_operator_in_domain:
  assumes g:
      "Elem g (pp_t_domain (Prop \<rightarrow>\<^sub>o Prop))"
  shows "Elem (pp_t_cone_extend_prop_operator s g)
    (pp_t_domain (Prop \<rightarrow>\<^sub>o Prop))"
  unfolding pp_t_cone_extend_prop_operator_def
proof (rule pp_t_lambda_closed)
  fix P
  assume P: "Elem P (pp_t_domain Prop)"
  have image:
      "Elem (g \<acute> pp_t_cone_view s P) (pp_t_domain Prop)"
    using pp_t_app_closed[
      OF g pp_t_cone_view_in_domain] .
  show "Elem (pp_t_cone_lift s
      (g \<acute> pp_t_cone_view s P)) (pp_t_domain Prop)"
    by (rule pp_t_cone_lift_in_domain)
next
  fix w P Q
  assume P: "Elem P (pp_t_domain Prop)"
    and Q: "Elem Q (pp_t_domain Prop)"
    and PQ: "pp_t_eqv Prop w P Q"
  show "pp_t_eqv Prop w
      (pp_t_cone_lift s (g \<acute> pp_t_cone_view s P))
      (pp_t_cone_lift s (g \<acute> pp_t_cone_view s Q))"
    using pp_t_cone_extended_prop_operator_respects[
      OF g P Q PQ] .
qed

lemma pp_t_cone_extend_prop_operator_related:
  assumes g:
      "Elem g (pp_t_domain (Prop \<rightarrow>\<^sub>o Prop))"
  shows "pp_t_cone_rel (Prop \<rightarrow>\<^sub>o Prop) s
    (pp_t_cone_extend_prop_operator s g) g"
  unfolding pp_t_cone_rel.simps(3)
proof (intro allI impI)
  fix P Q
  assume P: "Elem P (pp_t_domain Prop)"
    and Q: "Elem Q (pp_t_domain Prop)"
    and PQ: "pp_t_cone_rel Prop s P Q"
  have views:
      "pp_t_eqv Prop []
        (pp_t_cone_view s P) Q"
    using PQ by auto
  have outputs:
      "pp_t_eqv Prop []
        (g \<acute> pp_t_cone_view s P) (g \<acute> Q)"
    using pp_t_arrow_member_respects[
      OF g pp_t_cone_view_in_domain Q views] .
  have image_view:
      "Elem (g \<acute> pp_t_cone_view s P) (pp_t_domain Prop)"
    using pp_t_app_closed[OF g pp_t_cone_view_in_domain] .
  have image_Q: "Elem (g \<acute> Q) (pp_t_domain Prop)"
    using pp_t_app_closed[OF g Q] .
  have lifted:
      "Elem
        (pp_t_cone_lift s
          (g \<acute> pp_t_cone_view s P))
        (pp_t_domain Prop)"
    by (rule pp_t_cone_lift_in_domain)
  have base_rel:
      "pp_t_cone_rel Prop s
        (pp_t_cone_lift s
          (g \<acute> pp_t_cone_view s P))
        (g \<acute> pp_t_cone_view s P)"
    unfolding pp_t_cone_lift_def
    by (rule pp_t_cone_rel_prop_lift)
  have outputs_rev:
      "pp_t_eqv Prop [] (g \<acute> Q)
        (g \<acute> pp_t_cone_view s P)"
    using pp_t_eqv_symmetric[
      OF image_view image_Q outputs] .
  have replaced:
      "pp_t_cone_rel Prop s
        (pp_t_cone_lift s
          (g \<acute> pp_t_cone_view s P))
        (g \<acute> Q)"
    using pp_t_cone_rel_replace_right[
      OF lifted image_view image_Q base_rel outputs_rev] .
  show "pp_t_cone_rel Prop s
      (pp_t_cone_extend_prop_operator s g \<acute> P)
      (g \<acute> Q)"
    using replaced P
    by (simp add: pp_t_cone_extend_prop_operator_def
        Lambda_app)
qed

lemma pp_t_cone_right_total_Prop_Prop:
  "pp_t_cone_right_total (Prop \<rightarrow>\<^sub>o Prop) s"
proof (unfold pp_t_cone_right_total_def, intro allI impI)
  fix g
  assume g: "Elem g (pp_t_domain (Prop \<rightarrow>\<^sub>o Prop))"
  show "\<exists>f.
      Elem f (pp_t_domain (Prop \<rightarrow>\<^sub>o Prop)) \<and>
      pp_t_cone_rel (Prop \<rightarrow>\<^sub>o Prop) s f g"
    using pp_t_cone_extend_prop_operator_in_domain[OF g]
      pp_t_cone_extend_prop_operator_related[OF g]
    by blast
qed

subsection \<open>Recursive restriction and supported extension\<close>

fun pp_t_cone_restrict ::
    "otype \<Rightarrow> bool list \<Rightarrow> ZF \<Rightarrow> ZF"
and pp_t_cone_extend ::
    "otype \<Rightarrow> bool list \<Rightarrow> ZF \<Rightarrow> ZF"
where
  "pp_t_cone_restrict Ind s x = x"
| "pp_t_cone_restrict Prop s P = pp_t_cone_view s P"
| "pp_t_cone_restrict (\<sigma> \<rightarrow>\<^sub>o \<tau>) s f =
    Lambda (pp_t_domain \<sigma>)
      (\<lambda>y. pp_t_cone_restrict \<tau> s
        (f \<acute> pp_t_cone_extend \<sigma> s y))"
| "pp_t_cone_extend Ind s y = y"
| "pp_t_cone_extend Prop s Q = pp_t_cone_lift s Q"
| "pp_t_cone_extend (\<sigma> \<rightarrow>\<^sub>o \<tau>) s g =
    Lambda (pp_t_domain \<sigma>)
      (\<lambda>x. pp_t_cone_extend \<tau> s
        (g \<acute> pp_t_cone_restrict \<sigma> s x))"

lemma pp_t_cone_extend_Prop_Prop:
  "pp_t_cone_extend (Prop \<rightarrow>\<^sub>o Prop) s g =
    pp_t_cone_extend_prop_operator s g"
  by (simp add: pp_t_cone_extend_prop_operator_def)

lemma pp_t_cone_extend_Prop_Prop_in_domain:
  assumes "Elem g (pp_t_domain (Prop \<rightarrow>\<^sub>o Prop))"
  shows "Elem (pp_t_cone_extend (Prop \<rightarrow>\<^sub>o Prop) s g)
    (pp_t_domain (Prop \<rightarrow>\<^sub>o Prop))"
  apply (subst pp_t_cone_extend_Prop_Prop)
  using pp_t_cone_extend_prop_operator_in_domain[OF assms] .

lemma pp_t_cone_extend_Prop_Prop_related:
  assumes "Elem g (pp_t_domain (Prop \<rightarrow>\<^sub>o Prop))"
  shows "pp_t_cone_rel (Prop \<rightarrow>\<^sub>o Prop) s
    (pp_t_cone_extend (Prop \<rightarrow>\<^sub>o Prop) s g) g"
  apply (subst pp_t_cone_extend_Prop_Prop)
  using pp_t_cone_extend_prop_operator_related[OF assms] .

lemma pp_t_cone_restrict_Prop_Prop_in_domain:
  assumes f: "Elem f (pp_t_domain (Prop \<rightarrow>\<^sub>o Prop))"
  shows "Elem (pp_t_cone_restrict (Prop \<rightarrow>\<^sub>o Prop) s f)
    (pp_t_domain (Prop \<rightarrow>\<^sub>o Prop))"
  unfolding pp_t_cone_restrict.simps
  apply (rule pp_t_lambda_closed)
  subgoal for Q
    by (rule pp_t_cone_view_in_domain)
  subgoal for w Q R
  proof -
    assume Q: "Elem Q (pp_t_domain Prop)"
      and R: "Elem R (pp_t_domain Prop)"
      and QR: "pp_t_eqv Prop w Q R"
    have lifts:
        "pp_t_eqv Prop (s @ w)
          (pp_t_cone_lift s Q) (pp_t_cone_lift s R)"
      using pp_t_cone_lift_preserves_eqv[OF QR] .
    have outputs:
        "pp_t_eqv Prop (s @ w)
          (f \<acute> pp_t_cone_lift s Q)
          (f \<acute> pp_t_cone_lift s R)"
      using pp_t_arrow_member_respects[
        OF f pp_t_cone_lift_in_domain
          pp_t_cone_lift_in_domain lifts] .
    show ?thesis
      using pp_t_cone_view_preserves_eqv[OF outputs]
      by simp
  qed
  done

lemma pp_t_cone_restrict_Prop_Prop_related:
  assumes f: "Elem f (pp_t_domain (Prop \<rightarrow>\<^sub>o Prop))"
  shows "pp_t_cone_rel (Prop \<rightarrow>\<^sub>o Prop) s f
    (pp_t_cone_restrict (Prop \<rightarrow>\<^sub>o Prop) s f)"
  unfolding pp_t_cone_rel.simps(3)
proof (intro allI impI)
  fix P Q
  assume P: "Elem P (pp_t_domain Prop)"
    and Q: "Elem Q (pp_t_domain Prop)"
    and PQ: "pp_t_cone_rel Prop s P Q"
  have P_lift:
      "pp_t_eqv Prop s P (pp_t_cone_lift s Q)"
    using PQ
    by (auto simp: pp_t_cone_lift_holds prefix_def)
  have outputs:
      "pp_t_eqv Prop s (f \<acute> P)
        (f \<acute> pp_t_cone_lift s Q)"
    using pp_t_arrow_member_respects[
      OF f P pp_t_cone_lift_in_domain P_lift] .
  show "pp_t_cone_rel Prop s (f \<acute> P)
      (pp_t_cone_restrict (Prop \<rightarrow>\<^sub>o Prop) s f
        \<acute> Q)"
    using outputs Q
    by (auto simp: pp_t_cone_restrict.simps Lambda_app)
qed

subsection \<open>Sibling-cone components\<close>

text \<open>
  Supported extension is constant off its supporting cone at proposition
  type, but no such collapse is possible at individual type.  The correct
  type-sensitive invariant is connectivity through the two immediate
  sibling cones.  At individual type this reduces to equality; at
  proposition type every pair is connected.  Most importantly, the
  invariant is closed under application at every higher type.
\<close>

definition pp_t_sibling_component ::
    "otype \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> bool"
where
  "pp_t_sibling_component \<sigma> x y \<longleftrightarrow>
    Elem x (pp_t_domain \<sigma>) \<and>
    Elem y (pp_t_domain \<sigma>) \<and>
    (\<exists>z. Elem z (pp_t_domain \<sigma>) \<and>
      pp_t_eqv \<sigma> [False] x z \<and>
      pp_t_eqv \<sigma> [True] z y)"

lemma pp_t_sibling_componentD:
  assumes "pp_t_sibling_component \<sigma> x y"
  shows "Elem x (pp_t_domain \<sigma>)"
    and "Elem y (pp_t_domain \<sigma>)"
    and "\<exists>z. Elem z (pp_t_domain \<sigma>) \<and>
      pp_t_eqv \<sigma> [False] x z \<and>
      pp_t_eqv \<sigma> [True] z y"
  using assms unfolding pp_t_sibling_component_def by blast+

lemma pp_t_sibling_component_refl:
  assumes x: "Elem x (pp_t_domain \<sigma>)"
  shows "pp_t_sibling_component \<sigma> x x"
  unfolding pp_t_sibling_component_def
  using x pp_t_eqv_reflexive[OF x, of "[False]"]
    pp_t_eqv_reflexive[OF x, of "[True]"]
  by blast

lemma pp_t_sibling_component_app:
  assumes fg:
      "pp_t_sibling_component (\<sigma> \<rightarrow>\<^sub>o \<tau>) f g"
    and xy: "pp_t_sibling_component \<sigma> x y"
  shows "pp_t_sibling_component \<tau> (f \<acute> x) (g \<acute> y)"
proof -
  obtain h where h:
      "Elem h (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    and fh:
      "pp_t_eqv (\<sigma> \<rightarrow>\<^sub>o \<tau>) [False] f h"
    and hg:
      "pp_t_eqv (\<sigma> \<rightarrow>\<^sub>o \<tau>) [True] h g"
    using pp_t_sibling_componentD(3)[OF fg] by blast
  obtain z where z: "Elem z (pp_t_domain \<sigma>)"
    and xz: "pp_t_eqv \<sigma> [False] x z"
    and zy: "pp_t_eqv \<sigma> [True] z y"
    using pp_t_sibling_componentD(3)[OF xy] by blast
  have f: "Elem f (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    using pp_t_sibling_componentD(1)[OF fg] .
  have g: "Elem g (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    using pp_t_sibling_componentD(2)[OF fg] .
  have x: "Elem x (pp_t_domain \<sigma>)"
    using pp_t_sibling_componentD(1)[OF xy] .
  have y: "Elem y (pp_t_domain \<sigma>)"
    using pp_t_sibling_componentD(2)[OF xy] .
  have left:
      "pp_t_eqv \<tau> [False] (f \<acute> x) (h \<acute> z)"
    using pp_t_app_respects[OF fh x z xz] .
  have right:
      "pp_t_eqv \<tau> [True] (h \<acute> z) (g \<acute> y)"
    using pp_t_app_respects[OF hg z y zy] .
  have fx: "Elem (f \<acute> x) (pp_t_domain \<tau>)"
    using pp_t_app_closed[OF f x] .
  have gy: "Elem (g \<acute> y) (pp_t_domain \<tau>)"
    using pp_t_app_closed[OF g y] .
  have hz: "Elem (h \<acute> z) (pp_t_domain \<tau>)"
    using pp_t_app_closed[OF h z] .
  show ?thesis
    unfolding pp_t_sibling_component_def
    using fx gy hz left right by blast
qed

lemma pp_t_sibling_component_preserved:
  assumes f: "Elem f (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    and xy: "pp_t_sibling_component \<sigma> x y"
  shows "pp_t_sibling_component \<tau> (f \<acute> x) (f \<acute> y)"
  using pp_t_sibling_component_app[
      OF pp_t_sibling_component_refl[OF f] xy] .

lemma pp_t_sibling_component_Ind_iff:
  "pp_t_sibling_component Ind x y \<longleftrightarrow>
    Elem x (pp_t_domain Ind) \<and>
    Elem y (pp_t_domain Ind) \<and> x = y"
  unfolding pp_t_sibling_component_def by auto

definition pp_t_sibling_merge_prop :: "ZF \<Rightarrow> ZF \<Rightarrow> ZF"
where
  "pp_t_sibling_merge_prop P Q =
    pp_t_prop (\<lambda>v.
      if prefix [False] v then pp_t_holds P v
      else if prefix [True] v then pp_t_holds Q v
      else False)"

lemma pp_t_sibling_merge_prop_in_domain:
  "Elem (pp_t_sibling_merge_prop P Q) (pp_t_domain Prop)"
  unfolding pp_t_sibling_merge_prop_def
  using pp_t_prop_in_power by simp

lemma pp_t_sibling_merge_prop_left:
  "pp_t_eqv Prop [False] P (pp_t_sibling_merge_prop P Q)"
  unfolding pp_t_sibling_merge_prop_def
  by simp

lemma pp_t_sibling_merge_prop_right:
  "pp_t_eqv Prop [True] (pp_t_sibling_merge_prop P Q) Q"
proof (unfold pp_t_eqv.simps, intro allI impI)
  fix v
  assume true_v: "prefix [True] v"
  have not_false: "\<not> prefix [False] v"
  proof
    assume false_v: "prefix [False] v"
    have "prefix [False] [True] \<or> prefix [True] [False]"
      using prefix_same_cases[OF false_v true_v] .
    then show False by auto
  qed
  show "pp_t_holds (pp_t_sibling_merge_prop P Q) v
      \<longleftrightarrow> pp_t_holds Q v"
    using true_v not_false
    by (simp add: pp_t_sibling_merge_prop_def)
qed

lemma pp_t_sibling_component_Prop:
  assumes P: "Elem P (pp_t_domain Prop)"
    and Q: "Elem Q (pp_t_domain Prop)"
  shows "pp_t_sibling_component Prop P Q"
  unfolding pp_t_sibling_component_def
  using P Q pp_t_sibling_merge_prop_in_domain
    pp_t_sibling_merge_prop_left
    pp_t_sibling_merge_prop_right
  by blast

fun pp_t_sibling_merge ::
    "otype \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> ZF"
where
  "pp_t_sibling_merge Ind x y = x"
| "pp_t_sibling_merge Prop P Q = pp_t_sibling_merge_prop P Q"
| "pp_t_sibling_merge (\<sigma> \<rightarrow>\<^sub>o \<tau>) f g =
    Lambda (pp_t_domain \<sigma>)
      (\<lambda>x. pp_t_sibling_merge \<tau> (f \<acute> x) (g \<acute> x))"

fun pp_t_logical_component ::
    "otype \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> bool"
where
  "pp_t_logical_component Ind x y = (x = y)"
| "pp_t_logical_component Prop P Q = True"
| "pp_t_logical_component (\<sigma> \<rightarrow>\<^sub>o \<tau>) f g =
    (\<forall>x y.
      Elem x (pp_t_domain \<sigma>) \<longrightarrow>
      Elem y (pp_t_domain \<sigma>) \<longrightarrow>
      pp_t_sibling_component \<sigma> x y \<longrightarrow>
      pp_t_sibling_component \<tau> (f \<acute> x) (g \<acute> y))"

lemma pp_t_sibling_component_implies_logical:
  assumes comp: "pp_t_sibling_component \<sigma> x y"
  shows "pp_t_logical_component \<sigma> x y"
proof (cases \<sigma>)
  case Ind
  then show ?thesis
    using comp pp_t_sibling_component_Ind_iff by simp
next
  case Prop
  then show ?thesis by simp
next
  case (Arr \<sigma> \<tau>)
  then show ?thesis
    using comp pp_t_sibling_component_app by auto
qed

lemma pp_t_sibling_merge_congruent:
  assumes x: "Elem x (pp_t_domain \<sigma>)"
    and x': "Elem x' (pp_t_domain \<sigma>)"
    and y: "Elem y (pp_t_domain \<sigma>)"
    and y': "Elem y' (pp_t_domain \<sigma>)"
    and xx': "pp_t_eqv \<sigma> w x x'"
    and yy': "pp_t_eqv \<sigma> w y y'"
  shows "pp_t_eqv \<sigma> w
    (pp_t_sibling_merge \<sigma> x y)
    (pp_t_sibling_merge \<sigma> x' y')"
  using assms
proof (induction \<sigma> arbitrary: w x x' y y')
  case Ind
  then show ?case by simp
next
  case Prop
  show ?case
    unfolding pp_t_eqv.simps
  proof (intro allI impI)
    fix v
    assume future: "prefix w v"
    have xx_v:
        "pp_t_holds x v \<longleftrightarrow> pp_t_holds x' v"
      using Prop.prems(5) future by auto
    have yy_v:
        "pp_t_holds y v \<longleftrightarrow> pp_t_holds y' v"
      using Prop.prems(6) future by auto
    show "pp_t_holds (pp_t_sibling_merge Prop x y) v
        \<longleftrightarrow>
        pp_t_holds (pp_t_sibling_merge Prop x' y') v"
      using xx_v yy_v
      by (simp add: pp_t_sibling_merge_prop_def)
  qed
next
  case (Arr \<sigma> \<tau>)
  have x_fun:
      "Elem x (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    using Arr.prems(1) .
  have x'_fun:
      "Elem x' (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    using Arr.prems(2) .
  have y_fun:
      "Elem y (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    using Arr.prems(3) .
  have y'_fun:
      "Elem y' (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    using Arr.prems(4) .
  show ?case
    unfolding pp_t_eqv.simps
  proof (intro allI impI)
    fix v a b
    assume future: "prefix w v"
      and a: "Elem a (pp_t_domain \<sigma>)"
      and b: "Elem b (pp_t_domain \<sigma>)"
      and ab: "pp_t_eqv \<sigma> v a b"
    have left:
        "pp_t_eqv \<tau> v (x \<acute> a) (x' \<acute> b)"
      using Arr.prems(5) future a b ab by auto
    have right:
        "pp_t_eqv \<tau> v (y \<acute> a) (y' \<acute> b)"
      using Arr.prems(6) future a b ab by auto
    have xa: "Elem (x \<acute> a) (pp_t_domain \<tau>)"
      using pp_t_app_closed[OF x_fun a] .
    have x'b: "Elem (x' \<acute> b) (pp_t_domain \<tau>)"
      using pp_t_app_closed[OF x'_fun b] .
    have ya: "Elem (y \<acute> a) (pp_t_domain \<tau>)"
      using pp_t_app_closed[OF y_fun a] .
    have y'b: "Elem (y' \<acute> b) (pp_t_domain \<tau>)"
      using pp_t_app_closed[OF y'_fun b] .
    have target_ih:
        "Elem (x \<acute> a) (pp_t_domain \<tau>) \<Longrightarrow>
        Elem (x' \<acute> b) (pp_t_domain \<tau>) \<Longrightarrow>
        Elem (y \<acute> a) (pp_t_domain \<tau>) \<Longrightarrow>
        Elem (y' \<acute> b) (pp_t_domain \<tau>) \<Longrightarrow>
        pp_t_eqv \<tau> v (x \<acute> a) (x' \<acute> b) \<Longrightarrow>
        pp_t_eqv \<tau> v (y \<acute> a) (y' \<acute> b) \<Longrightarrow>
        pp_t_eqv \<tau> v
          (pp_t_sibling_merge \<tau> (x \<acute> a) (y \<acute> a))
          (pp_t_sibling_merge \<tau> (x' \<acute> b) (y' \<acute> b))"
      using Arr.IH(2) by blast
    show "pp_t_eqv \<tau> v
        (pp_t_sibling_merge
          (\<sigma> \<rightarrow>\<^sub>o \<tau>) x y \<acute> a)
        (pp_t_sibling_merge
          (\<sigma> \<rightarrow>\<^sub>o \<tau>) x' y' \<acute> b)"
      using target_ih[OF xa x'b ya y'b left right] a b
      by (simp add: Lambda_app)
  qed
qed

lemma pp_t_logical_component_merge_package:
  assumes x: "Elem x (pp_t_domain \<sigma>)"
    and y: "Elem y (pp_t_domain \<sigma>)"
    and logical: "pp_t_logical_component \<sigma> x y"
  shows
    "Elem (pp_t_sibling_merge \<sigma> x y) (pp_t_domain \<sigma>)
    \<and> pp_t_eqv \<sigma> [False] x
      (pp_t_sibling_merge \<sigma> x y)
    \<and> pp_t_eqv \<sigma> [True]
      (pp_t_sibling_merge \<sigma> x y) y"
  using assms
proof (induction \<sigma> arbitrary: x y)
  case Ind
  then show ?case by simp
next
  case Prop
  then show ?case
    using pp_t_sibling_merge_prop_in_domain
      pp_t_sibling_merge_prop_left
      pp_t_sibling_merge_prop_right
    by simp
next
  case (Arr \<sigma> \<tau>)
  let ?h = "pp_t_sibling_merge (\<sigma> \<rightarrow>\<^sub>o \<tau>) x y"
  have x_fun:
      "Elem x (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    using Arr.prems(1) .
  have y_fun:
      "Elem y (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    using Arr.prems(2) .
  have cross:
      "\<And>a b. Elem a (pp_t_domain \<sigma>) \<Longrightarrow>
        Elem b (pp_t_domain \<sigma>) \<Longrightarrow>
        pp_t_sibling_component \<sigma> a b \<Longrightarrow>
        pp_t_sibling_component \<tau> (x \<acute> a) (y \<acute> b)"
    using Arr.prems(3) by simp
  have output_component:
      "\<And>a. Elem a (pp_t_domain \<sigma>) \<Longrightarrow>
        pp_t_sibling_component \<tau> (x \<acute> a) (y \<acute> a)"
  proof -
    fix a
    assume a: "Elem a (pp_t_domain \<sigma>)"
    show "pp_t_sibling_component \<tau> (x \<acute> a) (y \<acute> a)"
      using cross[OF a a pp_t_sibling_component_refl[OF a]] .
  qed
  have output_merge_domain:
      "\<And>a. Elem a (pp_t_domain \<sigma>) \<Longrightarrow>
        Elem (pp_t_sibling_merge \<tau> (x \<acute> a) (y \<acute> a))
          (pp_t_domain \<tau>)"
  proof -
    fix a
    assume a: "Elem a (pp_t_domain \<sigma>)"
    have xa: "Elem (x \<acute> a) (pp_t_domain \<tau>)"
      using pp_t_app_closed[OF x_fun a] .
    have ya: "Elem (y \<acute> a) (pp_t_domain \<tau>)"
      using pp_t_app_closed[OF y_fun a] .
    have out_logical:
        "pp_t_logical_component \<tau> (x \<acute> a) (y \<acute> a)"
      using pp_t_sibling_component_implies_logical[
        OF output_component[OF a]] .
    show "Elem (pp_t_sibling_merge \<tau> (x \<acute> a) (y \<acute> a))
        (pp_t_domain \<tau>)"
      using Arr.IH(2)[OF xa ya out_logical] by blast
  qed
  have h_domain:
      "Elem ?h (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    unfolding pp_t_sibling_merge.simps
    apply (rule pp_t_lambda_closed)
    subgoal for a
      using output_merge_domain[of a] .
    subgoal for w a b
    proof -
      assume a: "Elem a (pp_t_domain \<sigma>)"
        and b: "Elem b (pp_t_domain \<sigma>)"
        and ab: "pp_t_eqv \<sigma> w a b"
      have xa: "Elem (x \<acute> a) (pp_t_domain \<tau>)"
        using pp_t_app_closed[OF x_fun a] .
      have xb: "Elem (x \<acute> b) (pp_t_domain \<tau>)"
        using pp_t_app_closed[OF x_fun b] .
      have ya: "Elem (y \<acute> a) (pp_t_domain \<tau>)"
        using pp_t_app_closed[OF y_fun a] .
      have yb: "Elem (y \<acute> b) (pp_t_domain \<tau>)"
        using pp_t_app_closed[OF y_fun b] .
      have xab: "pp_t_eqv \<tau> w (x \<acute> a) (x \<acute> b)"
        using pp_t_arrow_member_respects[OF x_fun a b ab] .
      have yab: "pp_t_eqv \<tau> w (y \<acute> a) (y \<acute> b)"
        using pp_t_arrow_member_respects[OF y_fun a b ab] .
      show ?thesis
        using pp_t_sibling_merge_congruent[
          OF xa xb ya yb xab yab] .
    qed
    done
  have left: "pp_t_eqv (\<sigma> \<rightarrow>\<^sub>o \<tau>) [False] x ?h"
    unfolding pp_t_eqv.simps
  proof (intro allI impI)
    fix v a b
    assume future: "prefix [False] v"
      and a: "Elem a (pp_t_domain \<sigma>)"
      and b: "Elem b (pp_t_domain \<sigma>)"
      and ab: "pp_t_eqv \<sigma> v a b"
    have xb: "Elem (x \<acute> b) (pp_t_domain \<tau>)"
      using pp_t_app_closed[OF x_fun b] .
    have yb: "Elem (y \<acute> b) (pp_t_domain \<tau>)"
      using pp_t_app_closed[OF y_fun b] .
    have out_logical:
        "pp_t_logical_component \<tau> (x \<acute> b) (y \<acute> b)"
      using pp_t_sibling_component_implies_logical[
        OF output_component[OF b]] .
    have branch:
        "pp_t_eqv \<tau> [False] (x \<acute> b)
          (pp_t_sibling_merge \<tau> (x \<acute> b) (y \<acute> b))"
      using Arr.IH(2)[OF xb yb out_logical] by blast
    have branch_v:
        "pp_t_eqv \<tau> v (x \<acute> b)
          (pp_t_sibling_merge \<tau> (x \<acute> b) (y \<acute> b))"
      using pp_t_eqv_persistent[OF branch future] .
    have xab: "pp_t_eqv \<tau> v (x \<acute> a) (x \<acute> b)"
      using pp_t_arrow_member_respects[OF x_fun a b ab] .
    have xa: "Elem (x \<acute> a) (pp_t_domain \<tau>)"
      using pp_t_app_closed[OF x_fun a] .
    have merged:
        "Elem (pp_t_sibling_merge \<tau> (x \<acute> b) (y \<acute> b))
          (pp_t_domain \<tau>)"
      using output_merge_domain[OF b] .
    show "pp_t_eqv \<tau> v (x \<acute> a) (?h \<acute> b)"
      using pp_t_eqv_transitive[
        OF xa xb merged xab branch_v] b
      by (simp add: Lambda_app)
  qed
  have right: "pp_t_eqv (\<sigma> \<rightarrow>\<^sub>o \<tau>) [True] ?h y"
    unfolding pp_t_eqv.simps
  proof (intro allI impI)
    fix v a b
    assume future: "prefix [True] v"
      and a: "Elem a (pp_t_domain \<sigma>)"
      and b: "Elem b (pp_t_domain \<sigma>)"
      and ab: "pp_t_eqv \<sigma> v a b"
    have xa: "Elem (x \<acute> a) (pp_t_domain \<tau>)"
      using pp_t_app_closed[OF x_fun a] .
    have ya: "Elem (y \<acute> a) (pp_t_domain \<tau>)"
      using pp_t_app_closed[OF y_fun a] .
    have yb: "Elem (y \<acute> b) (pp_t_domain \<tau>)"
      using pp_t_app_closed[OF y_fun b] .
    have out_logical:
        "pp_t_logical_component \<tau> (x \<acute> a) (y \<acute> a)"
      using pp_t_sibling_component_implies_logical[
        OF output_component[OF a]] .
    have branch:
        "pp_t_eqv \<tau> [True]
          (pp_t_sibling_merge \<tau> (x \<acute> a) (y \<acute> a))
          (y \<acute> a)"
      using Arr.IH(2)[OF xa ya out_logical] by blast
    have branch_v:
        "pp_t_eqv \<tau> v
          (pp_t_sibling_merge \<tau> (x \<acute> a) (y \<acute> a))
          (y \<acute> a)"
      using pp_t_eqv_persistent[OF branch future] .
    have yab: "pp_t_eqv \<tau> v (y \<acute> a) (y \<acute> b)"
      using pp_t_arrow_member_respects[OF y_fun a b ab] .
    have merged:
        "Elem (pp_t_sibling_merge \<tau> (x \<acute> a) (y \<acute> a))
          (pp_t_domain \<tau>)"
      using output_merge_domain[OF a] .
    show "pp_t_eqv \<tau> v (?h \<acute> a) (y \<acute> b)"
      using pp_t_eqv_transitive[
        OF merged ya yb branch_v yab] a
      by (simp add: Lambda_app)
  qed
  show ?case
    using h_domain left right by blast
qed

lemma pp_t_logical_component_merge:
  assumes x: "Elem x (pp_t_domain \<sigma>)"
    and y: "Elem y (pp_t_domain \<sigma>)"
    and logical: "pp_t_logical_component \<sigma> x y"
  shows
    "Elem (pp_t_sibling_merge \<sigma> x y) (pp_t_domain \<sigma>)"
    "pp_t_eqv \<sigma> [False] x
      (pp_t_sibling_merge \<sigma> x y)"
    "pp_t_eqv \<sigma> [True]
      (pp_t_sibling_merge \<sigma> x y) y"
  using pp_t_logical_component_merge_package[OF x y logical]
  by blast+

lemma pp_t_logical_component_implies_sibling:
  assumes x: "Elem x (pp_t_domain \<sigma>)"
    and y: "Elem y (pp_t_domain \<sigma>)"
    and logical: "pp_t_logical_component \<sigma> x y"
  shows "pp_t_sibling_component \<sigma> x y"
  unfolding pp_t_sibling_component_def
  using x y pp_t_logical_component_merge[OF x y logical]
  by blast

theorem pp_t_sibling_component_iff_logical:
  assumes x: "Elem x (pp_t_domain \<sigma>)"
    and y: "Elem y (pp_t_domain \<sigma>)"
  shows "pp_t_sibling_component \<sigma> x y
    \<longleftrightarrow> pp_t_logical_component \<sigma> x y"
  using pp_t_sibling_component_implies_logical
    pp_t_logical_component_implies_sibling[OF x y]
  by blast

subsection \<open>The support relation\<close>

definition pp_t_support_rel ::
    "otype \<Rightarrow> bool list \<Rightarrow> bool list \<Rightarrow>
      ZF \<Rightarrow> ZF \<Rightarrow> bool"
where
  "pp_t_support_rel \<sigma> s w x y \<longleftrightarrow>
    (if prefix s w then
      (\<exists>u. w = s @ u \<and> pp_t_eqv \<sigma> u x y)
    else if prefix w s then
      pp_t_eqv \<sigma> [] x y
    else
      pp_t_sibling_component \<sigma> x y)"

lemma pp_t_support_rel_inside_iff:
  "pp_t_support_rel \<sigma> s (s @ u) x y
    \<longleftrightarrow> pp_t_eqv \<sigma> u x y"
  unfolding pp_t_support_rel_def by simp

lemma pp_t_support_rel_above:
  assumes ws: "prefix w s"
    and xy: "pp_t_eqv \<sigma> [] x y"
  shows "pp_t_support_rel \<sigma> s w x y"
proof (cases "prefix s w")
  case True
  then have "s = w"
    using ws prefix_order.antisym by blast
  then show ?thesis
    using xy by (simp add: pp_t_support_rel_def)
next
  case False
  then show ?thesis
    using ws xy by (simp add: pp_t_support_rel_def)
qed

lemma pp_t_support_rel_outside:
  assumes sw: "\<not> prefix s w"
    and ws: "\<not> prefix w s"
    and xy: "pp_t_sibling_component \<sigma> x y"
  shows "pp_t_support_rel \<sigma> s w x y"
  using assms by (simp add: pp_t_support_rel_def)

lemma pp_t_incomparable_no_common_future:
  assumes sw: "\<not> prefix s w"
    and ws: "\<not> prefix w s"
    and wv: "prefix w v"
  shows "\<not> prefix s v"
proof
  assume sv: "prefix s v"
  have "prefix s w \<or> prefix w s"
    using prefix_same_cases[OF sv wv] .
  then show False using sw ws by blast
qed

lemma pp_t_root_eqv_implies_sibling_component:
  assumes x: "Elem x (pp_t_domain \<sigma>)"
    and y: "Elem y (pp_t_domain \<sigma>)"
    and xy: "pp_t_eqv \<sigma> [] x y"
  shows "pp_t_sibling_component \<sigma> x y"
proof -
  have left: "pp_t_eqv \<sigma> [False] x y"
    using pp_t_eqv_persistent[OF xy] by simp
  have right: "pp_t_eqv \<sigma> [True] y y"
    using pp_t_eqv_reflexive[OF y] .
  show ?thesis
    unfolding pp_t_sibling_component_def
    using x y left right by blast
qed

lemma pp_t_support_rel_preserved:
  assumes f: "Elem f (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    and xy: "pp_t_support_rel \<sigma> s w x y"
    and x: "Elem x (pp_t_domain \<sigma>)"
    and y: "Elem y (pp_t_domain \<sigma>)"
  shows "pp_t_support_rel \<tau> s w (f \<acute> x) (f \<acute> y)"
proof (cases "prefix s w")
  case True
  have exists:
      "\<exists>u. w = s @ u \<and> pp_t_eqv \<sigma> u x y"
    using xy True unfolding pp_t_support_rel_def by simp
  then obtain u where w: "w = s @ u"
    and local: "pp_t_eqv \<sigma> u x y"
    by blast
  have outputs:
      "pp_t_eqv \<tau> u (f \<acute> x) (f \<acute> y)"
    using pp_t_arrow_member_respects[OF f x y local] .
  show ?thesis
    using w outputs by (simp add: pp_t_support_rel_def)
next
  case not_inside: False
  show ?thesis
  proof (cases "prefix w s")
    case True
    have local: "pp_t_eqv \<sigma> [] x y"
      using xy not_inside True
      unfolding pp_t_support_rel_def by simp
    have outputs:
        "pp_t_eqv \<tau> [] (f \<acute> x) (f \<acute> y)"
      using pp_t_arrow_member_respects[OF f x y local] .
    show ?thesis
      using not_inside True outputs
      by (simp add: pp_t_support_rel_def)
  next
    case False
    have comp: "pp_t_sibling_component \<sigma> x y"
      using xy not_inside False
      unfolding pp_t_support_rel_def by simp
    have outputs:
        "pp_t_sibling_component \<tau> (f \<acute> x) (f \<acute> y)"
      using pp_t_sibling_component_preserved[OF f comp] .
    show ?thesis
      using not_inside False outputs
      by (simp add: pp_t_support_rel_def)
  qed
qed

lemma pp_t_support_rel_app:
  assumes fg:
      "pp_t_support_rel (\<sigma> \<rightarrow>\<^sub>o \<tau>) s w f g"
    and f: "Elem f (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    and g: "Elem g (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    and wv: "prefix w v"
    and xy: "pp_t_support_rel \<sigma> s v x y"
    and x: "Elem x (pp_t_domain \<sigma>)"
    and y: "Elem y (pp_t_domain \<sigma>)"
  shows "pp_t_support_rel \<tau> s v (f \<acute> x) (g \<acute> y)"
proof (cases "prefix s v")
  case inside: True
  then obtain t where v: "v = s @ t"
    by (auto simp: prefix_def)
  have args: "pp_t_eqv \<sigma> t x y"
    using xy v by (simp add: pp_t_support_rel_def)
  have comparable: "prefix s w \<or> prefix w s"
    using prefix_same_cases[OF inside wv] .
  have fun_eqv:
      "pp_t_eqv (\<sigma> \<rightarrow>\<^sub>o \<tau>) t f g"
  proof -
    from comparable show ?thesis
    proof
      assume sw: "prefix s w"
      then obtain u where w: "w = s @ u"
        by (auto simp: prefix_def)
      have ut: "prefix u t"
        using wv w v by simp
      have base:
          "pp_t_eqv (\<sigma> \<rightarrow>\<^sub>o \<tau>) u f g"
        using fg w by (simp add: pp_t_support_rel_def)
      show ?thesis
        using pp_t_eqv_persistent[OF base ut] .
    next
      assume ws: "prefix w s"
      have base:
          "pp_t_eqv (\<sigma> \<rightarrow>\<^sub>o \<tau>) [] f g"
        using fg ws
      proof (cases "prefix s w")
        case True
        then have "s = w"
          using ws prefix_order.antisym by blast
        then show ?thesis
          using fg by (simp add: pp_t_support_rel_def)
      next
        case False
        then show ?thesis
          using fg ws by (simp add: pp_t_support_rel_def)
      qed
      show ?thesis
        using pp_t_eqv_persistent[OF base] by simp
    qed
  qed
  have outputs:
      "pp_t_eqv \<tau> t (f \<acute> x) (g \<acute> y)"
    using pp_t_app_respects[OF fun_eqv x y args] .
  show ?thesis
    using v outputs by (simp add: pp_t_support_rel_def)
next
  case not_inside: False
  show ?thesis
  proof (cases "prefix v s")
    case above: True
    have args: "pp_t_eqv \<sigma> [] x y"
      using xy not_inside above
      by (simp add: pp_t_support_rel_def)
    have ws: "prefix w s"
      using prefix_order.trans[OF wv above] .
    have fun_eqv:
        "pp_t_eqv (\<sigma> \<rightarrow>\<^sub>o \<tau>) [] f g"
    proof (cases "prefix s w")
      case True
      then have "s = w"
        using ws prefix_order.antisym by blast
      then show ?thesis
        using fg by (simp add: pp_t_support_rel_def)
    next
      case False
      then show ?thesis
        using fg ws by (simp add: pp_t_support_rel_def)
    qed
    have outputs:
        "pp_t_eqv \<tau> [] (f \<acute> x) (g \<acute> y)"
      using pp_t_app_respects[OF fun_eqv x y args] .
    show ?thesis
      using not_inside above outputs
      by (simp add: pp_t_support_rel_def)
  next
    case not_above: False
    have args: "pp_t_sibling_component \<sigma> x y"
      using xy not_inside not_above
      by (simp add: pp_t_support_rel_def)
    have fun_comp:
        "pp_t_sibling_component (\<sigma> \<rightarrow>\<^sub>o \<tau>) f g"
    proof (cases "prefix s w")
      case True
      have "prefix s v"
        using True wv by (rule prefix_order.trans)
      then show ?thesis using not_inside by blast
    next
      case not_w_inside: False
      show ?thesis
      proof (cases "prefix w s")
        case True
        have root:
            "pp_t_eqv (\<sigma> \<rightarrow>\<^sub>o \<tau>) [] f g"
          using fg not_w_inside True
          by (simp add: pp_t_support_rel_def)
        show ?thesis
          using pp_t_root_eqv_implies_sibling_component[OF f g root] .
      next
        case False
        show ?thesis
          using fg not_w_inside False
          by (simp add: pp_t_support_rel_def)
      qed
    qed
    have outputs:
        "pp_t_sibling_component \<tau> (f \<acute> x) (g \<acute> y)"
      using pp_t_sibling_component_app[OF fun_comp args] .
    show ?thesis
      using not_inside not_above outputs
      by (simp add: pp_t_support_rel_def)
  qed
qed

lemma pp_t_cone_view_eqv_support:
  assumes P: "Elem P (pp_t_domain Prop)"
    and Q: "Elem Q (pp_t_domain Prop)"
    and PQ: "pp_t_eqv Prop w P Q"
  shows "pp_t_support_rel Prop s w
    (pp_t_cone_view s P) (pp_t_cone_view s Q)"
proof (cases "prefix s w")
  case True
  then obtain u where w: "w = s @ u"
    by (auto simp: prefix_def)
  have views:
      "pp_t_eqv Prop u
        (pp_t_cone_view s P) (pp_t_cone_view s Q)"
    using pp_t_cone_view_preserves_eqv[of s u P Q] PQ w
    by simp
  show ?thesis
    using w views by (simp add: pp_t_support_rel_def)
next
  case not_inside: False
  show ?thesis
  proof (cases "prefix w s")
    case True
    have at_s: "pp_t_eqv Prop s P Q"
      using pp_t_eqv_persistent[OF PQ True] .
    have views:
        "pp_t_eqv Prop []
          (pp_t_cone_view s P) (pp_t_cone_view s Q)"
      using pp_t_cone_view_preserves_eqv[
        of s "[]" P Q] at_s by simp
    show ?thesis
      using pp_t_support_rel_above[OF True views] .
  next
    case False
    have component:
        "pp_t_sibling_component Prop
          (pp_t_cone_view s P) (pp_t_cone_view s Q)"
      using pp_t_sibling_component_Prop[
        OF pp_t_cone_view_in_domain pp_t_cone_view_in_domain] .
    show ?thesis
      using pp_t_support_rel_outside[
        OF not_inside False component] .
  qed
qed

lemma pp_t_cone_lift_support_eqv:
  assumes QR: "pp_t_support_rel Prop s w Q R"
  shows "pp_t_eqv Prop w
    (pp_t_cone_lift s Q) (pp_t_cone_lift s R)"
proof (cases "prefix s w")
  case True
  then obtain u where w: "w = s @ u"
    by (auto simp: prefix_def)
  have local: "pp_t_eqv Prop u Q R"
    using QR w by (simp add: pp_t_support_rel_def)
  show ?thesis
    using pp_t_cone_lift_preserves_eqv[OF local] w by simp
next
  case not_inside: False
  show ?thesis
  proof (cases "prefix w s")
    case above: True
    have root: "pp_t_eqv Prop [] Q R"
      using QR not_inside above by (simp add: pp_t_support_rel_def)
    show ?thesis
      unfolding pp_t_eqv.simps
    proof (intro allI impI)
      fix v
      assume wv: "prefix w v"
      show "pp_t_holds (pp_t_cone_lift s Q) v
          \<longleftrightarrow> pp_t_holds (pp_t_cone_lift s R) v"
      proof (cases "prefix s v")
        case False
        then show ?thesis
          by (auto simp: pp_t_cone_lift_holds prefix_def)
      next
        case True
        then obtain t where v: "v = s @ t"
          by (auto simp: prefix_def)
        have value_iff:
            "pp_t_holds Q t \<longleftrightarrow> pp_t_holds R t"
          using root by auto
        show ?thesis
          using value_iff v by (simp add: pp_t_cone_lift_holds)
      qed
    qed
  next
    case outside: False
    show ?thesis
      unfolding pp_t_eqv.simps
    proof (intro allI impI)
      fix v
      assume wv: "prefix w v"
      have not_sv: "\<not> prefix s v"
        using pp_t_incomparable_no_common_future[
          OF not_inside outside wv] .
      show "pp_t_holds (pp_t_cone_lift s Q) v
          \<longleftrightarrow> pp_t_holds (pp_t_cone_lift s R) v"
        using not_sv
        by (auto simp: pp_t_cone_lift_holds prefix_def)
    qed
  qed
qed

definition pp_t_cone_transform_invariant :: "otype \<Rightarrow> bool"
where
  "pp_t_cone_transform_invariant \<sigma> \<longleftrightarrow>
    (\<forall>s x. Elem x (pp_t_domain \<sigma>) \<longrightarrow>
      Elem (pp_t_cone_restrict \<sigma> s x) (pp_t_domain \<sigma>))
    \<and>
    (\<forall>s x. Elem x (pp_t_domain \<sigma>) \<longrightarrow>
      Elem (pp_t_cone_extend \<sigma> s x) (pp_t_domain \<sigma>))
    \<and>
    (\<forall>s w x y.
      Elem x (pp_t_domain \<sigma>) \<longrightarrow>
      Elem y (pp_t_domain \<sigma>) \<longrightarrow>
      pp_t_eqv \<sigma> w x y \<longrightarrow>
      pp_t_support_rel \<sigma> s w
        (pp_t_cone_restrict \<sigma> s x)
        (pp_t_cone_restrict \<sigma> s y))
    \<and>
    (\<forall>s w x y.
      Elem x (pp_t_domain \<sigma>) \<longrightarrow>
      Elem y (pp_t_domain \<sigma>) \<longrightarrow>
      pp_t_support_rel \<sigma> s w x y \<longrightarrow>
      pp_t_eqv \<sigma> w
        (pp_t_cone_extend \<sigma> s x)
        (pp_t_cone_extend \<sigma> s y))"

theorem pp_t_cone_transform_invariant_all:
  "pp_t_cone_transform_invariant \<sigma>"
proof (induction \<sigma>)
  case Ind
  show ?case
    unfolding pp_t_cone_transform_invariant_def
    by (auto simp: pp_t_support_rel_def
        pp_t_sibling_component_Ind_iff prefix_def)
next
  case Prop
  show ?case
    unfolding pp_t_cone_transform_invariant_def
    apply (intro conjI)
    subgoal
      by (intro allI impI;
          simp only: pp_t_cone_restrict.simps;
          rule pp_t_cone_view_in_domain)
    subgoal
      by (intro allI impI;
          simp only: pp_t_cone_extend.simps;
          rule pp_t_cone_lift_in_domain)
    subgoal
      by (simp only: pp_t_cone_restrict.simps;
          auto intro: pp_t_cone_view_eqv_support)
    subgoal
      apply (simp only: pp_t_cone_extend.simps)
      apply (intro allI impI)
      apply (rule pp_t_cone_lift_support_eqv)
      apply assumption
      done
    done
next
  case (Arr \<sigma> \<tau>)
  have arg_restrict_domain:
      "\<And>s x. Elem x (pp_t_domain \<sigma>) \<Longrightarrow>
        Elem (pp_t_cone_restrict \<sigma> s x)
          (pp_t_domain \<sigma>)"
    using Arr.IH(1)
    unfolding pp_t_cone_transform_invariant_def by blast
  have arg_extend_domain:
      "\<And>s x. Elem x (pp_t_domain \<sigma>) \<Longrightarrow>
        Elem (pp_t_cone_extend \<sigma> s x)
          (pp_t_domain \<sigma>)"
    using Arr.IH(1)
    unfolding pp_t_cone_transform_invariant_def by blast
  have arg_restrict_congruent:
      "\<And>s w x y.
        Elem x (pp_t_domain \<sigma>) \<Longrightarrow>
        Elem y (pp_t_domain \<sigma>) \<Longrightarrow>
        pp_t_eqv \<sigma> w x y \<Longrightarrow>
        pp_t_support_rel \<sigma> s w
          (pp_t_cone_restrict \<sigma> s x)
          (pp_t_cone_restrict \<sigma> s y)"
    using Arr.IH(1)
    unfolding pp_t_cone_transform_invariant_def by blast
  have arg_extend_congruent:
      "\<And>s w x y.
        Elem x (pp_t_domain \<sigma>) \<Longrightarrow>
        Elem y (pp_t_domain \<sigma>) \<Longrightarrow>
        pp_t_support_rel \<sigma> s w x y \<Longrightarrow>
        pp_t_eqv \<sigma> w
          (pp_t_cone_extend \<sigma> s x)
          (pp_t_cone_extend \<sigma> s y)"
    using Arr.IH(1)
    unfolding pp_t_cone_transform_invariant_def by blast
  have target_restrict_domain:
      "\<And>s x. Elem x (pp_t_domain \<tau>) \<Longrightarrow>
        Elem (pp_t_cone_restrict \<tau> s x)
          (pp_t_domain \<tau>)"
    using Arr.IH(2)
    unfolding pp_t_cone_transform_invariant_def by blast
  have target_extend_domain:
      "\<And>s x. Elem x (pp_t_domain \<tau>) \<Longrightarrow>
        Elem (pp_t_cone_extend \<tau> s x)
          (pp_t_domain \<tau>)"
    using Arr.IH(2)
    unfolding pp_t_cone_transform_invariant_def by blast
  have target_restrict_congruent:
      "\<And>s w x y.
        Elem x (pp_t_domain \<tau>) \<Longrightarrow>
        Elem y (pp_t_domain \<tau>) \<Longrightarrow>
        pp_t_eqv \<tau> w x y \<Longrightarrow>
        pp_t_support_rel \<tau> s w
          (pp_t_cone_restrict \<tau> s x)
          (pp_t_cone_restrict \<tau> s y)"
    using Arr.IH(2)
    unfolding pp_t_cone_transform_invariant_def by blast
  have target_extend_congruent:
      "\<And>s w x y.
        Elem x (pp_t_domain \<tau>) \<Longrightarrow>
        Elem y (pp_t_domain \<tau>) \<Longrightarrow>
        pp_t_support_rel \<tau> s w x y \<Longrightarrow>
        pp_t_eqv \<tau> w
          (pp_t_cone_extend \<tau> s x)
          (pp_t_cone_extend \<tau> s y)"
    using Arr.IH(2)
    unfolding pp_t_cone_transform_invariant_def by blast

  have restrict_domain:
      "\<And>s f.
        Elem f (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>)) \<Longrightarrow>
        Elem (pp_t_cone_restrict (\<sigma> \<rightarrow>\<^sub>o \<tau>) s f)
          (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
  proof -
    fix s f
    assume f:
        "Elem f (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    show "Elem
        (pp_t_cone_restrict (\<sigma> \<rightarrow>\<^sub>o \<tau>) s f)
        (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
      unfolding pp_t_cone_restrict.simps
    proof (rule pp_t_lambda_closed)
      fix y
      assume y: "Elem y (pp_t_domain \<sigma>)"
      have extended:
          "Elem (pp_t_cone_extend \<sigma> s y)
            (pp_t_domain \<sigma>)"
        using arg_extend_domain[OF y] .
      have output_value:
          "Elem (f \<acute> pp_t_cone_extend \<sigma> s y)
            (pp_t_domain \<tau>)"
        using pp_t_app_closed[OF f extended] .
      show "Elem
          (pp_t_cone_restrict \<tau> s
            (f \<acute> pp_t_cone_extend \<sigma> s y))
          (pp_t_domain \<tau>)"
        using target_restrict_domain[OF output_value] .
    next
      fix w y z
      assume y: "Elem y (pp_t_domain \<sigma>)"
        and z: "Elem z (pp_t_domain \<sigma>)"
        and yz: "pp_t_eqv \<sigma> w y z"
      have support:
          "pp_t_support_rel \<sigma> s (s @ w) y z"
        using yz by (simp add: pp_t_support_rel_inside_iff)
      have extended:
          "pp_t_eqv \<sigma> (s @ w)
            (pp_t_cone_extend \<sigma> s y)
            (pp_t_cone_extend \<sigma> s z)"
        using arg_extend_congruent[OF y z support] .
      have ey:
          "Elem (pp_t_cone_extend \<sigma> s y)
            (pp_t_domain \<sigma>)"
        using arg_extend_domain[OF y] .
      have ez:
          "Elem (pp_t_cone_extend \<sigma> s z)
            (pp_t_domain \<sigma>)"
        using arg_extend_domain[OF z] .
      have outputs:
          "pp_t_eqv \<tau> (s @ w)
            (f \<acute> pp_t_cone_extend \<sigma> s y)
            (f \<acute> pp_t_cone_extend \<sigma> s z)"
        using pp_t_arrow_member_respects[OF f ey ez extended] .
      have fy:
          "Elem (f \<acute> pp_t_cone_extend \<sigma> s y)
            (pp_t_domain \<tau>)"
        using pp_t_app_closed[OF f ey] .
      have fz:
          "Elem (f \<acute> pp_t_cone_extend \<sigma> s z)
            (pp_t_domain \<tau>)"
        using pp_t_app_closed[OF f ez] .
      have restricted:
          "pp_t_support_rel \<tau> s (s @ w)
            (pp_t_cone_restrict \<tau> s
              (f \<acute> pp_t_cone_extend \<sigma> s y))
            (pp_t_cone_restrict \<tau> s
              (f \<acute> pp_t_cone_extend \<sigma> s z))"
        using target_restrict_congruent[OF fy fz outputs] .
      show "pp_t_eqv \<tau> w
          (pp_t_cone_restrict \<tau> s
            (f \<acute> pp_t_cone_extend \<sigma> s y))
          (pp_t_cone_restrict \<tau> s
            (f \<acute> pp_t_cone_extend \<sigma> s z))"
        using restricted by (simp add: pp_t_support_rel_inside_iff)
    qed
  qed

  have extend_domain:
      "\<And>s g.
        Elem g (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>)) \<Longrightarrow>
        Elem (pp_t_cone_extend (\<sigma> \<rightarrow>\<^sub>o \<tau>) s g)
          (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
  proof -
    fix s g
    assume g:
        "Elem g (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    show "Elem
        (pp_t_cone_extend (\<sigma> \<rightarrow>\<^sub>o \<tau>) s g)
        (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
      unfolding pp_t_cone_extend.simps
    proof (rule pp_t_lambda_closed)
      fix x
      assume x: "Elem x (pp_t_domain \<sigma>)"
      have restricted:
          "Elem (pp_t_cone_restrict \<sigma> s x)
            (pp_t_domain \<sigma>)"
        using arg_restrict_domain[OF x] .
      have output_value:
          "Elem (g \<acute> pp_t_cone_restrict \<sigma> s x)
            (pp_t_domain \<tau>)"
        using pp_t_app_closed[OF g restricted] .
      show "Elem
          (pp_t_cone_extend \<tau> s
            (g \<acute> pp_t_cone_restrict \<sigma> s x))
          (pp_t_domain \<tau>)"
        using target_extend_domain[OF output_value] .
    next
      fix w x y
      assume x: "Elem x (pp_t_domain \<sigma>)"
        and y: "Elem y (pp_t_domain \<sigma>)"
        and xy: "pp_t_eqv \<sigma> w x y"
      have restricted_x:
          "Elem (pp_t_cone_restrict \<sigma> s x)
            (pp_t_domain \<sigma>)"
        using arg_restrict_domain[OF x] .
      have restricted_y:
          "Elem (pp_t_cone_restrict \<sigma> s y)
            (pp_t_domain \<sigma>)"
        using arg_restrict_domain[OF y] .
      have support:
          "pp_t_support_rel \<sigma> s w
            (pp_t_cone_restrict \<sigma> s x)
            (pp_t_cone_restrict \<sigma> s y)"
        using arg_restrict_congruent[OF x y xy] .
      have output_support:
          "pp_t_support_rel \<tau> s w
            (g \<acute> pp_t_cone_restrict \<sigma> s x)
            (g \<acute> pp_t_cone_restrict \<sigma> s y)"
        using pp_t_support_rel_preserved[
          OF g support restricted_x restricted_y] .
      have gx:
          "Elem (g \<acute> pp_t_cone_restrict \<sigma> s x)
            (pp_t_domain \<tau>)"
        using pp_t_app_closed[OF g restricted_x] .
      have gy:
          "Elem (g \<acute> pp_t_cone_restrict \<sigma> s y)
            (pp_t_domain \<tau>)"
        using pp_t_app_closed[OF g restricted_y] .
      show "pp_t_eqv \<tau> w
          (pp_t_cone_extend \<tau> s
            (g \<acute> pp_t_cone_restrict \<sigma> s x))
          (pp_t_cone_extend \<tau> s
            (g \<acute> pp_t_cone_restrict \<sigma> s y))"
        using target_extend_congruent[OF gx gy output_support] .
    qed
  qed

  have restrict_local:
      "\<And>s u f g.
        Elem f (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>)) \<Longrightarrow>
        Elem g (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>)) \<Longrightarrow>
        pp_t_eqv (\<sigma> \<rightarrow>\<^sub>o \<tau>) (s @ u) f g \<Longrightarrow>
        pp_t_eqv (\<sigma> \<rightarrow>\<^sub>o \<tau>) u
          (pp_t_cone_restrict (\<sigma> \<rightarrow>\<^sub>o \<tau>) s f)
          (pp_t_cone_restrict (\<sigma> \<rightarrow>\<^sub>o \<tau>) s g)"
  proof -
    fix s u f g
    assume f:
        "Elem f (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
      and g:
        "Elem g (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
      and fg:
        "pp_t_eqv (\<sigma> \<rightarrow>\<^sub>o \<tau>) (s @ u) f g"
    show "pp_t_eqv (\<sigma> \<rightarrow>\<^sub>o \<tau>) u
        (pp_t_cone_restrict (\<sigma> \<rightarrow>\<^sub>o \<tau>) s f)
        (pp_t_cone_restrict (\<sigma> \<rightarrow>\<^sub>o \<tau>) s g)"
      unfolding pp_t_eqv.simps
    proof (intro allI impI)
      fix v a b
      assume uv: "prefix u v"
        and a: "Elem a (pp_t_domain \<sigma>)"
        and b: "Elem b (pp_t_domain \<sigma>)"
        and ab: "pp_t_eqv \<sigma> v a b"
      have support:
          "pp_t_support_rel \<sigma> s (s @ v) a b"
        using ab by (simp add: pp_t_support_rel_inside_iff)
      have extended:
          "pp_t_eqv \<sigma> (s @ v)
            (pp_t_cone_extend \<sigma> s a)
            (pp_t_cone_extend \<sigma> s b)"
        using arg_extend_congruent[OF a b support] .
      have ea:
          "Elem (pp_t_cone_extend \<sigma> s a)
            (pp_t_domain \<sigma>)"
        using arg_extend_domain[OF a] .
      have eb:
          "Elem (pp_t_cone_extend \<sigma> s b)
            (pp_t_domain \<sigma>)"
        using arg_extend_domain[OF b] .
      have future: "prefix (s @ u) (s @ v)"
        using uv by (auto simp: prefix_def append_assoc)
      have outputs:
          "pp_t_eqv \<tau> (s @ v)
            (f \<acute> pp_t_cone_extend \<sigma> s a)
            (g \<acute> pp_t_cone_extend \<sigma> s b)"
        using fg future ea eb extended by auto
      have fa:
          "Elem (f \<acute> pp_t_cone_extend \<sigma> s a)
            (pp_t_domain \<tau>)"
        using pp_t_app_closed[OF f ea] .
      have gb:
          "Elem (g \<acute> pp_t_cone_extend \<sigma> s b)
            (pp_t_domain \<tau>)"
        using pp_t_app_closed[OF g eb] .
      have restricted:
          "pp_t_support_rel \<tau> s (s @ v)
            (pp_t_cone_restrict \<tau> s
              (f \<acute> pp_t_cone_extend \<sigma> s a))
            (pp_t_cone_restrict \<tau> s
              (g \<acute> pp_t_cone_extend \<sigma> s b))"
        using target_restrict_congruent[OF fa gb outputs] .
      have local:
          "pp_t_eqv \<tau> v
            (pp_t_cone_restrict \<tau> s
              (f \<acute> pp_t_cone_extend \<sigma> s a))
            (pp_t_cone_restrict \<tau> s
              (g \<acute> pp_t_cone_extend \<sigma> s b))"
        using restricted by (simp add: pp_t_support_rel_inside_iff)
      show "pp_t_eqv \<tau> v
          (pp_t_cone_restrict (\<sigma> \<rightarrow>\<^sub>o \<tau>) s f
            \<acute> a)
          (pp_t_cone_restrict (\<sigma> \<rightarrow>\<^sub>o \<tau>) s g
            \<acute> b)"
        using local a b by (simp add: Lambda_app)
    qed
  qed

  have restrict_congruent:
      "\<And>s w f g.
        Elem f (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>)) \<Longrightarrow>
        Elem g (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>)) \<Longrightarrow>
        pp_t_eqv (\<sigma> \<rightarrow>\<^sub>o \<tau>) w f g \<Longrightarrow>
        pp_t_support_rel (\<sigma> \<rightarrow>\<^sub>o \<tau>) s w
          (pp_t_cone_restrict (\<sigma> \<rightarrow>\<^sub>o \<tau>) s f)
          (pp_t_cone_restrict (\<sigma> \<rightarrow>\<^sub>o \<tau>) s g)"
  proof -
    fix s w f g
    assume f:
        "Elem f (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
      and g:
        "Elem g (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
      and fg:
        "pp_t_eqv (\<sigma> \<rightarrow>\<^sub>o \<tau>) w f g"
    have rf:
        "Elem (pp_t_cone_restrict (\<sigma> \<rightarrow>\<^sub>o \<tau>) s f)
          (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
      using restrict_domain[OF f] .
    have rg:
        "Elem (pp_t_cone_restrict (\<sigma> \<rightarrow>\<^sub>o \<tau>) s g)
          (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
      using restrict_domain[OF g] .
    show "pp_t_support_rel (\<sigma> \<rightarrow>\<^sub>o \<tau>) s w
        (pp_t_cone_restrict (\<sigma> \<rightarrow>\<^sub>o \<tau>) s f)
        (pp_t_cone_restrict (\<sigma> \<rightarrow>\<^sub>o \<tau>) s g)"
    proof (cases "prefix s w")
      case True
      then obtain u where w: "w = s @ u"
        by (auto simp: prefix_def)
      have local:
          "pp_t_eqv (\<sigma> \<rightarrow>\<^sub>o \<tau>) u
            (pp_t_cone_restrict (\<sigma> \<rightarrow>\<^sub>o \<tau>) s f)
            (pp_t_cone_restrict (\<sigma> \<rightarrow>\<^sub>o \<tau>) s g)"
        using restrict_local[OF f g] fg w by simp
      show ?thesis
        using w local by (simp add: pp_t_support_rel_def)
    next
      case not_inside: False
      show ?thesis
      proof (cases "prefix w s")
        case above: True
        have at_s:
            "pp_t_eqv (\<sigma> \<rightarrow>\<^sub>o \<tau>) s f g"
          using pp_t_eqv_persistent[OF fg above] .
        have at_s_append:
            "pp_t_eqv (\<sigma> \<rightarrow>\<^sub>o \<tau>) (s @ []) f g"
          using at_s by simp
        have root:
            "pp_t_eqv (\<sigma> \<rightarrow>\<^sub>o \<tau>) []
              (pp_t_cone_restrict
                (\<sigma> \<rightarrow>\<^sub>o \<tau>) s f)
              (pp_t_cone_restrict
                (\<sigma> \<rightarrow>\<^sub>o \<tau>) s g)"
          using restrict_local[OF f g at_s_append] .
        show ?thesis
          using pp_t_support_rel_above[OF above root] .
      next
        case outside: False
        have logical:
            "pp_t_logical_component (\<sigma> \<rightarrow>\<^sub>o \<tau>)
              (pp_t_cone_restrict
                (\<sigma> \<rightarrow>\<^sub>o \<tau>) s f)
              (pp_t_cone_restrict
                (\<sigma> \<rightarrow>\<^sub>o \<tau>) s g)"
          unfolding pp_t_logical_component.simps
        proof (intro allI impI)
          fix a b
          assume a: "Elem a (pp_t_domain \<sigma>)"
            and b: "Elem b (pp_t_domain \<sigma>)"
            and ab: "pp_t_sibling_component \<sigma> a b"
          have support:
              "pp_t_support_rel \<sigma> s w a b"
            using pp_t_support_rel_outside[
              OF not_inside outside ab] .
          have extended:
              "pp_t_eqv \<sigma> w
                (pp_t_cone_extend \<sigma> s a)
                (pp_t_cone_extend \<sigma> s b)"
            using arg_extend_congruent[OF a b support] .
          have ea:
              "Elem (pp_t_cone_extend \<sigma> s a)
                (pp_t_domain \<sigma>)"
            using arg_extend_domain[OF a] .
          have eb:
              "Elem (pp_t_cone_extend \<sigma> s b)
                (pp_t_domain \<sigma>)"
            using arg_extend_domain[OF b] .
          have outputs:
              "pp_t_eqv \<tau> w
                (f \<acute> pp_t_cone_extend \<sigma> s a)
                (g \<acute> pp_t_cone_extend \<sigma> s b)"
            using pp_t_app_respects[OF fg ea eb extended] .
          have fa:
              "Elem (f \<acute> pp_t_cone_extend \<sigma> s a)
                (pp_t_domain \<tau>)"
            using pp_t_app_closed[OF f ea] .
          have gb:
              "Elem (g \<acute> pp_t_cone_extend \<sigma> s b)
                (pp_t_domain \<tau>)"
            using pp_t_app_closed[OF g eb] .
          have output_support:
              "pp_t_support_rel \<tau> s w
                (pp_t_cone_restrict \<tau> s
                  (f \<acute> pp_t_cone_extend \<sigma> s a))
                (pp_t_cone_restrict \<tau> s
                  (g \<acute> pp_t_cone_extend \<sigma> s b))"
            using target_restrict_congruent[OF fa gb outputs] .
          have component:
              "pp_t_sibling_component \<tau>
                (pp_t_cone_restrict \<tau> s
                  (f \<acute> pp_t_cone_extend \<sigma> s a))
                (pp_t_cone_restrict \<tau> s
                  (g \<acute> pp_t_cone_extend \<sigma> s b))"
            using output_support not_inside outside
            by (simp add: pp_t_support_rel_def)
          show "pp_t_sibling_component \<tau>
              (pp_t_cone_restrict
                (\<sigma> \<rightarrow>\<^sub>o \<tau>) s f \<acute> a)
              (pp_t_cone_restrict
                (\<sigma> \<rightarrow>\<^sub>o \<tau>) s g \<acute> b)"
            using component a b by (simp add: Lambda_app)
        qed
        have component:
            "pp_t_sibling_component (\<sigma> \<rightarrow>\<^sub>o \<tau>)
              (pp_t_cone_restrict
                (\<sigma> \<rightarrow>\<^sub>o \<tau>) s f)
              (pp_t_cone_restrict
                (\<sigma> \<rightarrow>\<^sub>o \<tau>) s g)"
          using pp_t_logical_component_implies_sibling[
            OF rf rg logical] .
        show ?thesis
          using pp_t_support_rel_outside[
            OF not_inside outside component] .
      qed
    qed
  qed

  have extend_congruent:
      "\<And>s w f g.
        Elem f (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>)) \<Longrightarrow>
        Elem g (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>)) \<Longrightarrow>
        pp_t_support_rel (\<sigma> \<rightarrow>\<^sub>o \<tau>) s w f g \<Longrightarrow>
        pp_t_eqv (\<sigma> \<rightarrow>\<^sub>o \<tau>) w
          (pp_t_cone_extend (\<sigma> \<rightarrow>\<^sub>o \<tau>) s f)
          (pp_t_cone_extend (\<sigma> \<rightarrow>\<^sub>o \<tau>) s g)"
  proof -
    fix s w f g
    assume f:
        "Elem f (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
      and g:
        "Elem g (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
      and fg:
        "pp_t_support_rel (\<sigma> \<rightarrow>\<^sub>o \<tau>) s w f g"
    show "pp_t_eqv (\<sigma> \<rightarrow>\<^sub>o \<tau>) w
        (pp_t_cone_extend (\<sigma> \<rightarrow>\<^sub>o \<tau>) s f)
        (pp_t_cone_extend (\<sigma> \<rightarrow>\<^sub>o \<tau>) s g)"
      unfolding pp_t_eqv.simps
    proof (intro allI impI)
      fix v x y
      assume wv: "prefix w v"
        and x: "Elem x (pp_t_domain \<sigma>)"
        and y: "Elem y (pp_t_domain \<sigma>)"
        and xy: "pp_t_eqv \<sigma> v x y"
      have rx:
          "Elem (pp_t_cone_restrict \<sigma> s x)
            (pp_t_domain \<sigma>)"
        using arg_restrict_domain[OF x] .
      have ry:
          "Elem (pp_t_cone_restrict \<sigma> s y)
            (pp_t_domain \<sigma>)"
        using arg_restrict_domain[OF y] .
      have arg_support:
          "pp_t_support_rel \<sigma> s v
            (pp_t_cone_restrict \<sigma> s x)
            (pp_t_cone_restrict \<sigma> s y)"
        using arg_restrict_congruent[OF x y xy] .
      have output_support:
          "pp_t_support_rel \<tau> s v
            (f \<acute> pp_t_cone_restrict \<sigma> s x)
            (g \<acute> pp_t_cone_restrict \<sigma> s y)"
        using pp_t_support_rel_app[
          OF fg f g wv arg_support rx ry] .
      have fx:
          "Elem (f \<acute> pp_t_cone_restrict \<sigma> s x)
            (pp_t_domain \<tau>)"
        using pp_t_app_closed[OF f rx] .
      have gy:
          "Elem (g \<acute> pp_t_cone_restrict \<sigma> s y)
            (pp_t_domain \<tau>)"
        using pp_t_app_closed[OF g ry] .
      have extended:
          "pp_t_eqv \<tau> v
            (pp_t_cone_extend \<tau> s
              (f \<acute> pp_t_cone_restrict \<sigma> s x))
            (pp_t_cone_extend \<tau> s
              (g \<acute> pp_t_cone_restrict \<sigma> s y))"
        using target_extend_congruent[OF fx gy output_support] .
      show "pp_t_eqv \<tau> v
          (pp_t_cone_extend (\<sigma> \<rightarrow>\<^sub>o \<tau>) s f
            \<acute> x)
          (pp_t_cone_extend (\<sigma> \<rightarrow>\<^sub>o \<tau>) s g
            \<acute> y)"
        using extended x y by (simp add: Lambda_app)
    qed
  qed

  show ?case
    unfolding pp_t_cone_transform_invariant_def
    using restrict_domain extend_domain
      restrict_congruent extend_congruent
    by blast
qed

lemma pp_t_cone_restrict_in_domain:
  assumes x: "Elem x (pp_t_domain \<sigma>)"
  shows "Elem (pp_t_cone_restrict \<sigma> s x)
    (pp_t_domain \<sigma>)"
  using pp_t_cone_transform_invariant_all x
  unfolding pp_t_cone_transform_invariant_def by blast

lemma pp_t_cone_extend_in_domain:
  assumes x: "Elem x (pp_t_domain \<sigma>)"
  shows "Elem (pp_t_cone_extend \<sigma> s x)
    (pp_t_domain \<sigma>)"
  using pp_t_cone_transform_invariant_all x
  unfolding pp_t_cone_transform_invariant_def by blast

lemma pp_t_cone_restrict_congruent:
  assumes x: "Elem x (pp_t_domain \<sigma>)"
    and y: "Elem y (pp_t_domain \<sigma>)"
    and xy: "pp_t_eqv \<sigma> w x y"
  shows "pp_t_support_rel \<sigma> s w
    (pp_t_cone_restrict \<sigma> s x)
    (pp_t_cone_restrict \<sigma> s y)"
  using pp_t_cone_transform_invariant_all assms
  unfolding pp_t_cone_transform_invariant_def by blast

lemma pp_t_cone_extend_congruent:
  assumes x: "Elem x (pp_t_domain \<sigma>)"
    and y: "Elem y (pp_t_domain \<sigma>)"
    and xy: "pp_t_support_rel \<sigma> s w x y"
  shows "pp_t_eqv \<sigma> w
    (pp_t_cone_extend \<sigma> s x)
    (pp_t_cone_extend \<sigma> s y)"
  using pp_t_cone_transform_invariant_all assms
  unfolding pp_t_cone_transform_invariant_def by blast

definition pp_t_cone_canonical_invariant :: "otype \<Rightarrow> bool"
where
  "pp_t_cone_canonical_invariant \<sigma> \<longleftrightarrow>
    (\<forall>s x. Elem x (pp_t_domain \<sigma>) \<longrightarrow>
      pp_t_cone_rel \<sigma> s x
        (pp_t_cone_restrict \<sigma> s x))
    \<and>
    (\<forall>s y. Elem y (pp_t_domain \<sigma>) \<longrightarrow>
      pp_t_cone_rel \<sigma> s
        (pp_t_cone_extend \<sigma> s y) y)
    \<and>
    (\<forall>s. pp_t_cone_left_total \<sigma> s
      \<and> pp_t_cone_right_total \<sigma> s
      \<and> pp_t_cone_compatible \<sigma> s)"

theorem pp_t_cone_canonical_invariant_all:
  "pp_t_cone_canonical_invariant \<sigma>"
proof (induction \<sigma>)
  case Ind
  show ?case
    unfolding pp_t_cone_canonical_invariant_def
      pp_t_cone_left_total_def pp_t_cone_right_total_def
    using pp_t_cone_compatible_Ind by auto
next
  case Prop
  show ?case
    unfolding pp_t_cone_canonical_invariant_def
    apply (intro conjI)
    subgoal
      apply (intro allI impI)
      apply (simp only: pp_t_cone_restrict.simps)
      unfolding pp_t_cone_view_def
      by (rule pp_t_cone_rel_prop_view)
    subgoal
      apply (intro allI impI)
      apply (simp only: pp_t_cone_extend.simps)
      unfolding pp_t_cone_lift_def
      by (rule pp_t_cone_rel_prop_lift)
    subgoal
      apply (intro allI)
      using pp_t_cone_left_total_Prop
        pp_t_cone_right_total_Prop
        pp_t_cone_compatible_Prop by blast
    done
next
  case (Arr \<sigma> \<tau>)
  have arg_restrict_related:
      "\<And>s x. Elem x (pp_t_domain \<sigma>) \<Longrightarrow>
        pp_t_cone_rel \<sigma> s x
          (pp_t_cone_restrict \<sigma> s x)"
    using Arr.IH(1)
    unfolding pp_t_cone_canonical_invariant_def by blast
  have arg_extend_related:
      "\<And>s y. Elem y (pp_t_domain \<sigma>) \<Longrightarrow>
        pp_t_cone_rel \<sigma> s
          (pp_t_cone_extend \<sigma> s y) y"
    using Arr.IH(1)
    unfolding pp_t_cone_canonical_invariant_def by blast
  have arg_left: "\<And>s. pp_t_cone_left_total \<sigma> s"
    using Arr.IH(1)
    unfolding pp_t_cone_canonical_invariant_def by blast
  have arg_right: "\<And>s. pp_t_cone_right_total \<sigma> s"
    using Arr.IH(1)
    unfolding pp_t_cone_canonical_invariant_def by blast
  have arg_compatible: "\<And>s. pp_t_cone_compatible \<sigma> s"
    using Arr.IH(1)
    unfolding pp_t_cone_canonical_invariant_def by blast
  have target_restrict_related:
      "\<And>s x. Elem x (pp_t_domain \<tau>) \<Longrightarrow>
        pp_t_cone_rel \<tau> s x
          (pp_t_cone_restrict \<tau> s x)"
    using Arr.IH(2)
    unfolding pp_t_cone_canonical_invariant_def by blast
  have target_extend_related:
      "\<And>s y. Elem y (pp_t_domain \<tau>) \<Longrightarrow>
        pp_t_cone_rel \<tau> s
          (pp_t_cone_extend \<tau> s y) y"
    using Arr.IH(2)
    unfolding pp_t_cone_canonical_invariant_def by blast
  have target_left: "\<And>s. pp_t_cone_left_total \<tau> s"
    using Arr.IH(2)
    unfolding pp_t_cone_canonical_invariant_def by blast
  have target_right: "\<And>s. pp_t_cone_right_total \<tau> s"
    using Arr.IH(2)
    unfolding pp_t_cone_canonical_invariant_def by blast
  have target_compatible: "\<And>s. pp_t_cone_compatible \<tau> s"
    using Arr.IH(2)
    unfolding pp_t_cone_canonical_invariant_def by blast

  have restrict_related:
      "\<And>s f.
        Elem f (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>)) \<Longrightarrow>
        pp_t_cone_rel (\<sigma> \<rightarrow>\<^sub>o \<tau>) s f
          (pp_t_cone_restrict (\<sigma> \<rightarrow>\<^sub>o \<tau>) s f)"
  proof -
    fix s f
    assume f:
        "Elem f (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    show "pp_t_cone_rel (\<sigma> \<rightarrow>\<^sub>o \<tau>) s f
        (pp_t_cone_restrict (\<sigma> \<rightarrow>\<^sub>o \<tau>) s f)"
      unfolding pp_t_cone_rel.simps
    proof (intro allI impI)
      fix x y
      assume x: "Elem x (pp_t_domain \<sigma>)"
        and y: "Elem y (pp_t_domain \<sigma>)"
        and xy: "pp_t_cone_rel \<sigma> s x y"
      have ey:
          "Elem (pp_t_cone_extend \<sigma> s y)
            (pp_t_domain \<sigma>)"
        using pp_t_cone_extend_in_domain[OF y] .
      have extend_y:
          "pp_t_cone_rel \<sigma> s
            (pp_t_cone_extend \<sigma> s y) y"
        using arg_extend_related[OF y] .
      have x_extended:
          "pp_t_eqv \<sigma> s x
            (pp_t_cone_extend \<sigma> s y)"
      proof -
        have iff:
            "pp_t_eqv \<sigma> (s @ []) x
                (pp_t_cone_extend \<sigma> s y)
              \<longleftrightarrow> pp_t_eqv \<sigma> [] y y"
          using arg_compatible[of s]
            x y ey y xy extend_y
          unfolding pp_t_cone_compatible_def by blast
        have yy: "pp_t_eqv \<sigma> [] y y"
          using pp_t_eqv_reflexive[OF y] .
        show ?thesis using iff yy by simp
      qed
      have outputs:
          "pp_t_eqv \<tau> s (f \<acute> x)
            (f \<acute> pp_t_cone_extend \<sigma> s y)"
        using pp_t_arrow_member_respects[
          OF f x ey x_extended] .
      have fx: "Elem (f \<acute> x) (pp_t_domain \<tau>)"
        using pp_t_app_closed[OF f x] .
      have fey:
          "Elem (f \<acute> pp_t_cone_extend \<sigma> s y)
            (pp_t_domain \<tau>)"
        using pp_t_app_closed[OF f ey] .
      have target_rel:
          "pp_t_cone_rel \<tau> s
            (f \<acute> pp_t_cone_extend \<sigma> s y)
            (pp_t_cone_restrict \<tau> s
              (f \<acute> pp_t_cone_extend \<sigma> s y))"
        using target_restrict_related[OF fey] .
      have restricted:
          "Elem (pp_t_cone_restrict \<tau> s
              (f \<acute> pp_t_cone_extend \<sigma> s y))
            (pp_t_domain \<tau>)"
        using pp_t_cone_restrict_in_domain[OF fey] .
      have replaced:
          "pp_t_cone_rel \<tau> s (f \<acute> x)
            (pp_t_cone_restrict \<tau> s
              (f \<acute> pp_t_cone_extend \<sigma> s y))"
        using pp_t_cone_rel_replace_left[
          OF fey fx restricted target_rel outputs] .
      show "pp_t_cone_rel \<tau> s (f \<acute> x)
          (pp_t_cone_restrict
            (\<sigma> \<rightarrow>\<^sub>o \<tau>) s f \<acute> y)"
        using replaced y by (simp add: Lambda_app)
    qed
  qed

  have extend_related:
      "\<And>s g.
        Elem g (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>)) \<Longrightarrow>
        pp_t_cone_rel (\<sigma> \<rightarrow>\<^sub>o \<tau>) s
          (pp_t_cone_extend (\<sigma> \<rightarrow>\<^sub>o \<tau>) s g) g"
  proof -
    fix s g
    assume g:
        "Elem g (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    show "pp_t_cone_rel (\<sigma> \<rightarrow>\<^sub>o \<tau>) s
        (pp_t_cone_extend (\<sigma> \<rightarrow>\<^sub>o \<tau>) s g) g"
      unfolding pp_t_cone_rel.simps
    proof (intro allI impI)
      fix x y
      assume x: "Elem x (pp_t_domain \<sigma>)"
        and y: "Elem y (pp_t_domain \<sigma>)"
        and xy: "pp_t_cone_rel \<sigma> s x y"
      have rx:
          "Elem (pp_t_cone_restrict \<sigma> s x)
            (pp_t_domain \<sigma>)"
        using pp_t_cone_restrict_in_domain[OF x] .
      have restrict_x:
          "pp_t_cone_rel \<sigma> s x
            (pp_t_cone_restrict \<sigma> s x)"
        using arg_restrict_related[OF x] .
      have restricted_y:
          "pp_t_eqv \<sigma> []
            (pp_t_cone_restrict \<sigma> s x) y"
      proof -
        have iff:
            "pp_t_eqv \<sigma> (s @ []) x x
              \<longleftrightarrow>
              pp_t_eqv \<sigma> []
                (pp_t_cone_restrict \<sigma> s x) y"
          using arg_compatible[of s]
            x rx x y restrict_x xy
          unfolding pp_t_cone_compatible_def by blast
        have xx: "pp_t_eqv \<sigma> s x x"
          using pp_t_eqv_reflexive[OF x] .
        show ?thesis using iff xx by simp
      qed
      have outputs:
          "pp_t_eqv \<tau> []
            (g \<acute> pp_t_cone_restrict \<sigma> s x)
            (g \<acute> y)"
        using pp_t_arrow_member_respects[
          OF g rx y restricted_y] .
      have grx:
          "Elem (g \<acute> pp_t_cone_restrict \<sigma> s x)
            (pp_t_domain \<tau>)"
        using pp_t_app_closed[OF g rx] .
      have gy: "Elem (g \<acute> y) (pp_t_domain \<tau>)"
        using pp_t_app_closed[OF g y] .
      have target_rel:
          "pp_t_cone_rel \<tau> s
            (pp_t_cone_extend \<tau> s
              (g \<acute> pp_t_cone_restrict \<sigma> s x))
            (g \<acute> pp_t_cone_restrict \<sigma> s x)"
        using target_extend_related[OF grx] .
      have extended:
          "Elem (pp_t_cone_extend \<tau> s
              (g \<acute> pp_t_cone_restrict \<sigma> s x))
            (pp_t_domain \<tau>)"
        using pp_t_cone_extend_in_domain[OF grx] .
      have replaced:
          "pp_t_cone_rel \<tau> s
            (pp_t_cone_extend \<tau> s
              (g \<acute> pp_t_cone_restrict \<sigma> s x))
            (g \<acute> y)"
        using pp_t_cone_rel_replace_right[
          OF extended grx gy target_rel]
          pp_t_eqv_symmetric[OF grx gy outputs]
        by blast
      show "pp_t_cone_rel \<tau> s
          (pp_t_cone_extend
            (\<sigma> \<rightarrow>\<^sub>o \<tau>) s g \<acute> x)
          (g \<acute> y)"
        using replaced x by (simp add: Lambda_app)
    qed
  qed

  have left:
      "\<And>s. pp_t_cone_left_total (\<sigma> \<rightarrow>\<^sub>o \<tau>) s"
    unfolding pp_t_cone_left_total_def
    using pp_t_cone_restrict_in_domain restrict_related by blast
  have right:
      "\<And>s. pp_t_cone_right_total (\<sigma> \<rightarrow>\<^sub>o \<tau>) s"
    unfolding pp_t_cone_right_total_def
    using pp_t_cone_extend_in_domain extend_related by blast
  have compatible:
      "\<And>s. pp_t_cone_compatible (\<sigma> \<rightarrow>\<^sub>o \<tau>) s"
    using pp_t_cone_compatible_Arr[
      OF arg_left arg_right arg_compatible target_compatible] .
  show ?case
    unfolding pp_t_cone_canonical_invariant_def
    using restrict_related extend_related left right compatible
    by blast
qed

theorem pp_t_cone_restrict_related:
  assumes x: "Elem x (pp_t_domain \<sigma>)"
  shows "pp_t_cone_rel \<sigma> s x
    (pp_t_cone_restrict \<sigma> s x)"
  using pp_t_cone_canonical_invariant_all x
  unfolding pp_t_cone_canonical_invariant_def by blast

theorem pp_t_cone_extend_related:
  assumes y: "Elem y (pp_t_domain \<sigma>)"
  shows "pp_t_cone_rel \<sigma> s
    (pp_t_cone_extend \<sigma> s y) y"
  using pp_t_cone_canonical_invariant_all y
  unfolding pp_t_cone_canonical_invariant_def by blast

theorem pp_t_cone_left_total_all:
  "pp_t_cone_left_total \<sigma> s"
  using pp_t_cone_canonical_invariant_all
  unfolding pp_t_cone_canonical_invariant_def by blast

theorem pp_t_cone_right_total_all:
  "pp_t_cone_right_total \<sigma> s"
  using pp_t_cone_canonical_invariant_all
  unfolding pp_t_cone_canonical_invariant_def by blast

theorem pp_t_cone_compatible_all:
  "pp_t_cone_compatible \<sigma> s"
  using pp_t_cone_canonical_invariant_all
  unfolding pp_t_cone_canonical_invariant_def by blast

lemma pp_t_cone_rel_operator_implies_equivariant:
  assumes cone:
      "\<And>s. pp_t_cone_rel (Prop \<rightarrow>\<^sub>o Prop) s X X"
  shows "pp_b_equivariant (pp_b_operator_of X)"
proof (unfold pp_b_equivariant_def, intro allI)
  fix s P
  have inputs:
      "pp_t_cone_rel Prop s (pp_zf_of_b P)
        (pp_zf_of_b (pp_b_view s P))"
    using pp_t_cone_rel_prop_view[of s "pp_zf_of_b P"]
    by simp
  have left_domain:
      "Elem (pp_zf_of_b P) (pp_t_domain Prop)"
    by (rule pp_zf_of_b_in_domain)
  have right_domain:
      "Elem (pp_zf_of_b (pp_b_view s P)) (pp_t_domain Prop)"
    by (rule pp_zf_of_b_in_domain)
  have outputs:
      "pp_t_cone_rel Prop s
        (X \<acute> pp_zf_of_b P)
        (X \<acute> pp_zf_of_b (pp_b_view s P))"
    using cone[of s] left_domain right_domain inputs by auto
  show "pp_b_view s (pp_b_operator_of X P) =
      pp_b_operator_of X (pp_b_view s P)"
    using outputs
    by (auto simp: pp_b_view_def pp_b_operator_of_def
        pp_b_of_zf_def)
qed

locale pp_t_cone_totality =
  assumes left_total:
      "\<And>\<sigma> s. pp_t_cone_left_total \<sigma> s"
    and right_total:
      "\<And>\<sigma> s. pp_t_cone_right_total \<sigma> s"
begin

lemma pp_t_cone_rel_eqv_iff:
  assumes x: "Elem x (pp_t_domain \<sigma>)"
    and y: "Elem y (pp_t_domain \<sigma>)"
    and x': "Elem x' (pp_t_domain \<sigma>)"
    and y': "Elem y' (pp_t_domain \<sigma>)"
    and xy: "pp_t_cone_rel \<sigma> s x y"
    and x'y': "pp_t_cone_rel \<sigma> s x' y'"
  shows "pp_t_eqv \<sigma> (s @ u) x x'
    \<longleftrightarrow> pp_t_eqv \<sigma> u y y'"
  using assms
proof (induction \<sigma> arbitrary: s u x y x' y')
  case Ind
  then show ?case by simp
next
  case Prop
  then show ?case
    by (auto simp: prefix_def append_assoc)
next
  case (Arr \<sigma> \<tau>)
  show ?case
  proof
    assume left_eqv:
        "pp_t_eqv (\<sigma> \<rightarrow>\<^sub>o \<tau>) (s @ u) x x'"
    show "pp_t_eqv (\<sigma> \<rightarrow>\<^sub>o \<tau>) u y y'"
      unfolding pp_t_eqv.simps
    proof (intro allI impI)
      fix v b b'
      assume future: "prefix u v"
        and b: "Elem b (pp_t_domain \<sigma>)"
        and b': "Elem b' (pp_t_domain \<sigma>)"
        and bb': "pp_t_eqv \<sigma> v b b'"
      obtain a where a: "Elem a (pp_t_domain \<sigma>)"
        and ab: "pp_t_cone_rel \<sigma> s a b"
        using right_total[of \<sigma> s] b
        unfolding pp_t_cone_right_total_def by blast
      obtain a' where a': "Elem a' (pp_t_domain \<sigma>)"
        and a'b': "pp_t_cone_rel \<sigma> s a' b'"
        using right_total[of \<sigma> s] b'
        unfolding pp_t_cone_right_total_def by blast
      have aa': "pp_t_eqv \<sigma> (s @ v) a a'"
        using Arr.IH(1)[OF a b a' b' ab a'b', of v] bb'
        by blast
      have cone_future: "prefix (s @ u) (s @ v)"
        using future by (auto simp: prefix_def append_assoc)
      have left_outputs:
          "pp_t_eqv \<tau> (s @ v) (x \<acute> a) (x' \<acute> a')"
        using left_eqv cone_future a a' aa' by auto
      have xb:
          "pp_t_cone_rel \<tau> s (x \<acute> a) (y \<acute> b)"
        using Arr.prems(5) a b ab by auto
      have x'b':
          "pp_t_cone_rel \<tau> s (x' \<acute> a') (y' \<acute> b')"
        using Arr.prems(6) a' b' a'b' by auto
      have xa: "Elem (x \<acute> a) (pp_t_domain \<tau>)"
        using pp_t_app_closed[OF Arr.prems(1) a] .
      have yb: "Elem (y \<acute> b) (pp_t_domain \<tau>)"
        using pp_t_app_closed[OF Arr.prems(2) b] .
      have x'a': "Elem (x' \<acute> a') (pp_t_domain \<tau>)"
        using pp_t_app_closed[OF Arr.prems(3) a'] .
      have y'b': "Elem (y' \<acute> b') (pp_t_domain \<tau>)"
        using pp_t_app_closed[OF Arr.prems(4) b'] .
      show "pp_t_eqv \<tau> v (y \<acute> b) (y' \<acute> b')"
        using Arr.IH(2)[
          OF xa yb x'a' y'b' xb x'b', of v] left_outputs
        by blast
    qed
  next
    assume right_eqv:
        "pp_t_eqv (\<sigma> \<rightarrow>\<^sub>o \<tau>) u y y'"
    show "pp_t_eqv (\<sigma> \<rightarrow>\<^sub>o \<tau>) (s @ u) x x'"
      unfolding pp_t_eqv.simps
    proof (intro allI impI)
      fix z a a'
      assume future: "prefix (s @ u) z"
        and a: "Elem a (pp_t_domain \<sigma>)"
        and a': "Elem a' (pp_t_domain \<sigma>)"
        and aa': "pp_t_eqv \<sigma> z a a'"
      obtain t where z: "z = s @ t" and ut: "prefix u t"
        using future by (auto simp: prefix_def append_assoc)
      obtain b where b: "Elem b (pp_t_domain \<sigma>)"
        and ab: "pp_t_cone_rel \<sigma> s a b"
        using left_total[of \<sigma> s] a
        unfolding pp_t_cone_left_total_def by blast
      obtain b' where b': "Elem b' (pp_t_domain \<sigma>)"
        and a'b': "pp_t_cone_rel \<sigma> s a' b'"
        using left_total[of \<sigma> s] a'
        unfolding pp_t_cone_left_total_def by blast
      have bb': "pp_t_eqv \<sigma> t b b'"
        using Arr.IH(1)[OF a b a' b' ab a'b', of t]
          aa' z by blast
      have right_outputs:
          "pp_t_eqv \<tau> t (y \<acute> b) (y' \<acute> b')"
        using right_eqv ut b b' bb' by auto
      have xb:
          "pp_t_cone_rel \<tau> s (x \<acute> a) (y \<acute> b)"
        using Arr.prems(5) a b ab by auto
      have x'b':
          "pp_t_cone_rel \<tau> s (x' \<acute> a') (y' \<acute> b')"
        using Arr.prems(6) a' b' a'b' by auto
      have xa: "Elem (x \<acute> a) (pp_t_domain \<tau>)"
        using pp_t_app_closed[OF Arr.prems(1) a] .
      have yb: "Elem (y \<acute> b) (pp_t_domain \<tau>)"
        using pp_t_app_closed[OF Arr.prems(2) b] .
      have x'a': "Elem (x' \<acute> a') (pp_t_domain \<tau>)"
        using pp_t_app_closed[OF Arr.prems(3) a'] .
      have y'b': "Elem (y' \<acute> b') (pp_t_domain \<tau>)"
        using pp_t_app_closed[OF Arr.prems(4) b'] .
      show "pp_t_eqv \<tau> z (x \<acute> a) (x' \<acute> a')"
        using Arr.IH(2)[
          OF xa yb x'a' y'b' xb x'b', of t]
          right_outputs z by blast
    qed
  qed
qed

theorem pp_t_eval_cone_parametric:
  assumes typed: "\<Gamma> \<turnstile> M : \<tau>"
    and const_free: "consts_of M = {}"
    and env: "pp_t_cone_env_rel \<Gamma> s \<rho> \<eta>"
  shows "pp_t_cone_rel \<tau> s
    (pp_t_eval pp_t_default_constants \<rho> M)
    (pp_t_eval pp_t_default_constants \<eta> M)"
  using typed const_free env
proof (induction arbitrary: s \<rho> \<eta> rule: has_type.induct)
  case (Var \<Gamma> n \<tau>)
  show ?case
    using pp_t_cone_env_rel_lookup[
      OF Var.prems(2) Var.hyps] by simp
next
  case (Const \<Gamma> c \<tau>)
  then show ?case by simp
next
  case (App \<Gamma> M \<sigma> \<tau> N)
  have M_free: "consts_of M = {}"
    using App.prems(1) by simp
  have N_free: "consts_of N = {}"
    using App.prems(1) by simp
  have fun_rel:
      "pp_t_cone_rel (\<sigma> \<rightarrow>\<^sub>o \<tau>) s
        (pp_t_eval pp_t_default_constants \<rho> M)
        (pp_t_eval pp_t_default_constants \<eta> M)"
    using App.IH(1)[OF M_free App.prems(2)] .
  have arguments:
      "pp_t_cone_rel \<sigma> s
        (pp_t_eval pp_t_default_constants \<rho> N)
        (pp_t_eval pp_t_default_constants \<eta> N)"
    using App.IH(2)[OF N_free App.prems(2)] .
  have left_argument:
      "Elem (pp_t_eval pp_t_default_constants \<rho> N)
        (pp_t_domain \<sigma>)"
    using DefaultTreeConstants.pp_t_eval_type[
      OF App.hyps(2)
        pp_t_cone_env_rel_typed_left[OF App.prems(2)]]
    by (simp add: pp_t_dom_def)
  have right_argument:
      "Elem (pp_t_eval pp_t_default_constants \<eta> N)
        (pp_t_domain \<sigma>)"
    using DefaultTreeConstants.pp_t_eval_type[
      OF App.hyps(2)
        pp_t_cone_env_rel_typed_right[OF App.prems(2)]]
    by (simp add: pp_t_dom_def)
  show ?case
    using fun_rel left_argument right_argument arguments by simp
next
  case (Lam \<sigma> \<Gamma> M \<tau>)
  have body_free: "consts_of M = {}"
    using Lam.prems(1) by simp
  show ?case
    unfolding pp_t_eval.simps pp_t_cone_rel.simps
  proof (intro allI impI)
    fix x y
    assume x: "Elem x (pp_t_domain \<sigma>)"
      and y: "Elem y (pp_t_domain \<sigma>)"
      and xy: "pp_t_cone_rel \<sigma> s x y"
    have extended:
        "pp_t_cone_env_rel (\<sigma> # \<Gamma>) s
          (extend_env x \<rho>) (extend_env y \<eta>)"
      using pp_t_cone_env_rel_extend[
        OF Lam.prems(2) x y xy] .
    have body:
        "pp_t_cone_rel \<tau> s
          (pp_t_eval pp_t_default_constants
            (extend_env x \<rho>) M)
          (pp_t_eval pp_t_default_constants
            (extend_env y \<eta>) M)"
      using Lam.IH[OF body_free extended] .
    show "pp_t_cone_rel \<tau> s
        ((Lambda (pp_t_domain \<sigma>)
          (\<lambda>x. pp_t_eval pp_t_default_constants
            (extend_env x \<rho>) M)) \<acute> x)
        ((Lambda (pp_t_domain \<sigma>)
          (\<lambda>y. pp_t_eval pp_t_default_constants
            (extend_env y \<eta>) M)) \<acute> y)"
      using body x y by (simp add: Lambda_app)
  qed
next
  case (Eq \<Gamma> M \<sigma> N)
  have M_free: "consts_of M = {}"
    using Eq.prems(1) by simp
  have N_free: "consts_of N = {}"
    using Eq.prems(1) by simp
  have M_rel:
      "pp_t_cone_rel \<sigma> s
        (pp_t_eval pp_t_default_constants \<rho> M)
        (pp_t_eval pp_t_default_constants \<eta> M)"
    using Eq.IH(1)[OF M_free Eq.prems(2)] .
  have N_rel:
      "pp_t_cone_rel \<sigma> s
        (pp_t_eval pp_t_default_constants \<rho> N)
        (pp_t_eval pp_t_default_constants \<eta> N)"
    using Eq.IH(2)[OF N_free Eq.prems(2)] .
  have M_left:
      "Elem (pp_t_eval pp_t_default_constants \<rho> M)
        (pp_t_domain \<sigma>)"
    using DefaultTreeConstants.pp_t_eval_type[
      OF Eq.hyps(1)
        pp_t_cone_env_rel_typed_left[OF Eq.prems(2)]]
    by (simp add: pp_t_dom_def)
  have M_right:
      "Elem (pp_t_eval pp_t_default_constants \<eta> M)
        (pp_t_domain \<sigma>)"
    using DefaultTreeConstants.pp_t_eval_type[
      OF Eq.hyps(1)
        pp_t_cone_env_rel_typed_right[OF Eq.prems(2)]]
    by (simp add: pp_t_dom_def)
  have N_left:
      "Elem (pp_t_eval pp_t_default_constants \<rho> N)
        (pp_t_domain \<sigma>)"
    using DefaultTreeConstants.pp_t_eval_type[
      OF Eq.hyps(2)
        pp_t_cone_env_rel_typed_left[OF Eq.prems(2)]]
    by (simp add: pp_t_dom_def)
  have N_right:
      "Elem (pp_t_eval pp_t_default_constants \<eta> N)
        (pp_t_domain \<sigma>)"
    using DefaultTreeConstants.pp_t_eval_type[
      OF Eq.hyps(2)
        pp_t_cone_env_rel_typed_right[OF Eq.prems(2)]]
    by (simp add: pp_t_dom_def)
  show ?case
    unfolding pp_t_cone_rel.simps
  proof (intro allI)
    fix u
    show "pp_t_holds
          (pp_t_eval pp_t_default_constants \<rho> (Eq \<sigma> M N))
          (s @ u)
        \<longleftrightarrow>
        pp_t_holds
          (pp_t_eval pp_t_default_constants \<eta> (Eq \<sigma> M N)) u"
      unfolding pp_t_eval_Eq_holds
      using pp_t_cone_rel_eqv_iff[
        OF M_left M_right N_left N_right M_rel N_rel, of u] .
  qed
next
  case (Neg \<Gamma> A)
  have A_free: "consts_of A = {}"
    using Neg.prems(1) by simp
  have A_rel:
      "pp_t_cone_rel Prop s
        (pp_t_eval pp_t_default_constants \<rho> A)
        (pp_t_eval pp_t_default_constants \<eta> A)"
    using Neg.IH[OF A_free Neg.prems(2)] .
  show ?case
    using A_rel by simp
next
  case (Conj \<Gamma> A B)
  have A_free: "consts_of A = {}"
    and B_free: "consts_of B = {}"
    using Conj.prems(1) by simp_all
  have A_rel:
      "pp_t_cone_rel Prop s
        (pp_t_eval pp_t_default_constants \<rho> A)
        (pp_t_eval pp_t_default_constants \<eta> A)"
    using Conj.IH(1)[OF A_free Conj.prems(2)] .
  have B_rel:
      "pp_t_cone_rel Prop s
        (pp_t_eval pp_t_default_constants \<rho> B)
        (pp_t_eval pp_t_default_constants \<eta> B)"
    using Conj.IH(2)[OF B_free Conj.prems(2)] .
  show ?case
    using A_rel B_rel by simp
next
  case (Disj \<Gamma> A B)
  have A_free: "consts_of A = {}"
    and B_free: "consts_of B = {}"
    using Disj.prems(1) by simp_all
  have A_rel:
      "pp_t_cone_rel Prop s
        (pp_t_eval pp_t_default_constants \<rho> A)
        (pp_t_eval pp_t_default_constants \<eta> A)"
    using Disj.IH(1)[OF A_free Disj.prems(2)] .
  have B_rel:
      "pp_t_cone_rel Prop s
        (pp_t_eval pp_t_default_constants \<rho> B)
        (pp_t_eval pp_t_default_constants \<eta> B)"
    using Disj.IH(2)[OF B_free Disj.prems(2)] .
  show ?case
    using A_rel B_rel by simp
next
  case (Imp \<Gamma> A B)
  have A_free: "consts_of A = {}"
    and B_free: "consts_of B = {}"
    using Imp.prems(1) by simp_all
  have A_rel:
      "pp_t_cone_rel Prop s
        (pp_t_eval pp_t_default_constants \<rho> A)
        (pp_t_eval pp_t_default_constants \<eta> A)"
    using Imp.IH(1)[OF A_free Imp.prems(2)] .
  have B_rel:
      "pp_t_cone_rel Prop s
        (pp_t_eval pp_t_default_constants \<rho> B)
        (pp_t_eval pp_t_default_constants \<eta> B)"
    using Imp.IH(2)[OF B_free Imp.prems(2)] .
  show ?case
    using A_rel B_rel by simp
next
  case (Forall \<sigma> \<Gamma> A)
  have A_free: "consts_of A = {}"
    using Forall.prems(1) by simp
  have body_rel:
      "\<And>x y. Elem x (pp_t_domain \<sigma>) \<Longrightarrow>
        Elem y (pp_t_domain \<sigma>) \<Longrightarrow>
        pp_t_cone_rel \<sigma> s x y \<Longrightarrow>
        pp_t_cone_rel Prop s
          (pp_t_eval pp_t_default_constants
            (extend_env x \<rho>) A)
          (pp_t_eval pp_t_default_constants
            (extend_env y \<eta>) A)"
  proof -
    fix x y
    assume x: "Elem x (pp_t_domain \<sigma>)"
      and y: "Elem y (pp_t_domain \<sigma>)"
      and xy: "pp_t_cone_rel \<sigma> s x y"
    have extended:
        "pp_t_cone_env_rel (\<sigma> # \<Gamma>) s
          (extend_env x \<rho>) (extend_env y \<eta>)"
      using pp_t_cone_env_rel_extend[
        OF Forall.prems(2) x y xy] .
    show "pp_t_cone_rel Prop s
        (pp_t_eval pp_t_default_constants
          (extend_env x \<rho>) A)
        (pp_t_eval pp_t_default_constants
          (extend_env y \<eta>) A)"
      using Forall.IH[OF A_free extended] .
  qed
  show ?case
    unfolding pp_t_cone_rel.simps
  proof (intro allI)
    fix u
    show "pp_t_holds
          (pp_t_eval pp_t_default_constants \<rho>
            (Forall \<sigma> A)) (s @ u)
        \<longleftrightarrow>
        pp_t_holds
          (pp_t_eval pp_t_default_constants \<eta>
            (Forall \<sigma> A)) u"
      unfolding pp_t_eval_Forall_holds
    proof
      assume all_left:
          "\<forall>x. Elem x (pp_t_domain \<sigma>) \<longrightarrow>
            pp_t_holds
              (pp_t_eval pp_t_default_constants
                (extend_env x \<rho>) A) (s @ u)"
      show "\<forall>y. Elem y (pp_t_domain \<sigma>) \<longrightarrow>
          pp_t_holds
            (pp_t_eval pp_t_default_constants
              (extend_env y \<eta>) A) u"
      proof (intro allI impI)
        fix y
        assume y: "Elem y (pp_t_domain \<sigma>)"
        obtain x where x: "Elem x (pp_t_domain \<sigma>)"
          and xy: "pp_t_cone_rel \<sigma> s x y"
          using right_total[of \<sigma> s] y
          unfolding pp_t_cone_right_total_def by blast
        have related:
            "pp_t_cone_rel Prop s
              (pp_t_eval pp_t_default_constants
                (extend_env x \<rho>) A)
              (pp_t_eval pp_t_default_constants
                (extend_env y \<eta>) A)"
          using body_rel[OF x y xy] .
        show "pp_t_holds
            (pp_t_eval pp_t_default_constants
              (extend_env y \<eta>) A) u"
          using related all_left x by auto
      qed
    next
      assume all_right:
          "\<forall>y. Elem y (pp_t_domain \<sigma>) \<longrightarrow>
            pp_t_holds
              (pp_t_eval pp_t_default_constants
                (extend_env y \<eta>) A) u"
      show "\<forall>x. Elem x (pp_t_domain \<sigma>) \<longrightarrow>
          pp_t_holds
            (pp_t_eval pp_t_default_constants
              (extend_env x \<rho>) A) (s @ u)"
      proof (intro allI impI)
        fix x
        assume x: "Elem x (pp_t_domain \<sigma>)"
        obtain y where y: "Elem y (pp_t_domain \<sigma>)"
          and xy: "pp_t_cone_rel \<sigma> s x y"
          using left_total[of \<sigma> s] x
          unfolding pp_t_cone_left_total_def by blast
        have related:
            "pp_t_cone_rel Prop s
              (pp_t_eval pp_t_default_constants
                (extend_env x \<rho>) A)
              (pp_t_eval pp_t_default_constants
                (extend_env y \<eta>) A)"
          using body_rel[OF x y xy] .
        show "pp_t_holds
            (pp_t_eval pp_t_default_constants
              (extend_env x \<rho>) A) (s @ u)"
          using related all_right y by auto
      qed
    qed
  qed
next
  case (Exists \<sigma> \<Gamma> A)
  have A_free: "consts_of A = {}"
    using Exists.prems(1) by simp
  have body_rel:
      "\<And>x y. Elem x (pp_t_domain \<sigma>) \<Longrightarrow>
        Elem y (pp_t_domain \<sigma>) \<Longrightarrow>
        pp_t_cone_rel \<sigma> s x y \<Longrightarrow>
        pp_t_cone_rel Prop s
          (pp_t_eval pp_t_default_constants
            (extend_env x \<rho>) A)
          (pp_t_eval pp_t_default_constants
            (extend_env y \<eta>) A)"
  proof -
    fix x y
    assume x: "Elem x (pp_t_domain \<sigma>)"
      and y: "Elem y (pp_t_domain \<sigma>)"
      and xy: "pp_t_cone_rel \<sigma> s x y"
    have extended:
        "pp_t_cone_env_rel (\<sigma> # \<Gamma>) s
          (extend_env x \<rho>) (extend_env y \<eta>)"
      using pp_t_cone_env_rel_extend[
        OF Exists.prems(2) x y xy] .
    show "pp_t_cone_rel Prop s
        (pp_t_eval pp_t_default_constants
          (extend_env x \<rho>) A)
        (pp_t_eval pp_t_default_constants
          (extend_env y \<eta>) A)"
      using Exists.IH[OF A_free extended] .
  qed
  show ?case
    unfolding pp_t_cone_rel.simps
  proof (intro allI)
    fix u
    show "pp_t_holds
          (pp_t_eval pp_t_default_constants \<rho>
            (Exists \<sigma> A)) (s @ u)
        \<longleftrightarrow>
        pp_t_holds
          (pp_t_eval pp_t_default_constants \<eta>
            (Exists \<sigma> A)) u"
      unfolding pp_t_eval_Exists_holds
    proof
      assume some_left:
          "\<exists>x. Elem x (pp_t_domain \<sigma>) \<and>
            pp_t_holds
              (pp_t_eval pp_t_default_constants
                (extend_env x \<rho>) A) (s @ u)"
      then obtain x where x: "Elem x (pp_t_domain \<sigma>)"
        and true_left:
          "pp_t_holds
            (pp_t_eval pp_t_default_constants
              (extend_env x \<rho>) A) (s @ u)"
        by blast
      obtain y where y: "Elem y (pp_t_domain \<sigma>)"
        and xy: "pp_t_cone_rel \<sigma> s x y"
        using left_total[of \<sigma> s] x
        unfolding pp_t_cone_left_total_def by blast
      have related:
          "pp_t_cone_rel Prop s
            (pp_t_eval pp_t_default_constants
              (extend_env x \<rho>) A)
            (pp_t_eval pp_t_default_constants
              (extend_env y \<eta>) A)"
        using body_rel[OF x y xy] .
      have true_right:
          "pp_t_holds
            (pp_t_eval pp_t_default_constants
              (extend_env y \<eta>) A) u"
        using related true_left by auto
      show "\<exists>y. Elem y (pp_t_domain \<sigma>) \<and>
          pp_t_holds
            (pp_t_eval pp_t_default_constants
              (extend_env y \<eta>) A) u"
        using y true_right by blast
    next
      assume some_right:
          "\<exists>y. Elem y (pp_t_domain \<sigma>) \<and>
            pp_t_holds
              (pp_t_eval pp_t_default_constants
                (extend_env y \<eta>) A) u"
      then obtain y where y: "Elem y (pp_t_domain \<sigma>)"
        and true_right:
          "pp_t_holds
            (pp_t_eval pp_t_default_constants
              (extend_env y \<eta>) A) u"
        by blast
      obtain x where x: "Elem x (pp_t_domain \<sigma>)"
        and xy: "pp_t_cone_rel \<sigma> s x y"
        using right_total[of \<sigma> s] y
        unfolding pp_t_cone_right_total_def by blast
      have related:
          "pp_t_cone_rel Prop s
            (pp_t_eval pp_t_default_constants
              (extend_env x \<rho>) A)
            (pp_t_eval pp_t_default_constants
              (extend_env y \<eta>) A)"
        using body_rel[OF x y xy] .
      have true_left:
          "pp_t_holds
            (pp_t_eval pp_t_default_constants
              (extend_env x \<rho>) A) (s @ u)"
        using related true_right by auto
      show "\<exists>x. Elem x (pp_t_domain \<sigma>) \<and>
          pp_t_holds
            (pp_t_eval pp_t_default_constants
              (extend_env x \<rho>) A) (s @ u)"
        using x true_left by blast
    qed
  qed
qed

lemma pp_t_closed_env_cone_related:
  "pp_t_cone_env_rel [] s pp_t_closed_env pp_t_closed_env"
  by (simp add: pp_t_cone_env_rel_def pp_t_env_typed_def
      lookup_def)

theorem pp_t_closed_logical_den_cone_related:
  assumes typed: "[] \<turnstile> M : \<sigma>"
    and logical: "pp_logical_vocabulary M"
  shows "pp_t_cone_rel \<sigma> s
    (pp_t_closed_den M) (pp_t_closed_den M)"
proof -
  have const_free: "consts_of M = {}"
    using logical unfolding pp_logical_vocabulary_def .
  show ?thesis
    unfolding pp_t_closed_den_def
    using pp_t_eval_cone_parametric[
      OF typed const_free pp_t_closed_env_cone_related] .
qed

theorem pp_t_exact_closed_operator_equivariant:
  assumes X: "X \<in> pp_t_exact_closed_logical_operators"
  shows "pp_b_equivariant (pp_b_operator_of X)"
proof -
  obtain M where typed:
      "[] \<turnstile> M : (Prop \<rightarrow>\<^sub>o Prop)"
    and logical: "pp_logical_vocabulary M"
    and X_den: "X = pp_t_closed_den M"
    using X unfolding pp_t_exact_closed_logical_operators_def
    by blast
  have cone:
      "\<And>s. pp_t_cone_rel (Prop \<rightarrow>\<^sub>o Prop) s X X"
    using pp_t_closed_logical_den_cone_related[
      OF typed logical] X_den by blast
  show ?thesis
    using pp_t_cone_rel_operator_implies_equivariant[OF cone] .
qed

end

locale pp_t_closed_logical_cone_naturality =
  assumes closed_equivariant:
    "\<And>X. X \<in> pp_t_exact_closed_logical_operators \<Longrightarrow>
      pp_b_equivariant (pp_b_operator_of X)"
begin

theorem pp_t_generic_seed_for_exact_closed_operators:
  "\<exists>r. Elem r (pp_t_domain Prop) \<and>
    (\<forall>X \<in> pp_t_exact_closed_logical_operators.
      ((\<forall>w. pp_t_holds (X \<acute> r) w) \<longrightarrow>
       (\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
          pp_t_holds (X \<acute> q) [])))"
proof -
  have stock_equivariant:
      "\<And>F. F \<in> pp_b_closed_logical_operator_stock \<Longrightarrow>
        pp_b_equivariant F"
    using closed_equivariant
    unfolding pp_b_closed_logical_operator_stock_def by blast
  obtain R where generic:
      "\<forall>F \<in> pp_b_closed_logical_operator_stock.
        pp_b_root_unary_recombination F R"
    using pp_b_generic_witness_for_countable_stock[
      OF pp_b_closed_logical_operator_stock_countable
        stock_equivariant]
    by blast
  let ?r = "pp_zf_of_b R"
  show ?thesis
  proof (intro exI[of _ ?r] conjI ballI impI)
    show "Elem ?r (pp_t_domain Prop)"
      by (rule pp_zf_of_b_in_domain)
  next
    fix X
    assume X: "X \<in> pp_t_exact_closed_logical_operators"
    assume necessary: "\<forall>w. pp_t_holds (X \<acute> ?r) w"
    have operator_mem:
        "pp_b_operator_of X \<in>
          pp_b_closed_logical_operator_stock"
      using X
      unfolding pp_b_closed_logical_operator_stock_def by blast
    have recombines:
        "pp_b_root_unary_recombination
          (pp_b_operator_of X) R"
      using generic operator_mem by blast
    show "\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
        pp_t_holds (X \<acute> q) []"
      using pp_b_recombination_transfers_to_zf[
        OF recombines necessary] .
  qed
qed

theorem pp_t_generic_seed_recombines_closed_logical_stock_at_root:
  "\<exists>r. Elem r (pp_t_domain Prop) \<and>
    pp_t_unary_recombines_at
      (pp_t_closed_logical_stock (Prop \<rightarrow>\<^sub>o Prop))
      r []"
proof -
  obtain r where r: "Elem r (pp_t_domain Prop)"
    and exact_recombines:
      "\<forall>X \<in> pp_t_exact_closed_logical_operators.
        ((\<forall>w. pp_t_holds (X \<acute> r) w) \<longrightarrow>
         (\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
            pp_t_holds (X \<acute> q) []))"
    using pp_t_generic_seed_for_exact_closed_operators by blast
  show ?thesis
  proof (intro exI[of _ r] conjI)
    show "Elem r (pp_t_domain Prop)"
      using r .
    show "pp_t_unary_recombines_at
        (pp_t_closed_logical_stock (Prop \<rightarrow>\<^sub>o Prop))
        r []"
      unfolding pp_t_unary_recombines_at_def
    proof (intro allI impI)
      fix Y q
      assume Y: "Elem Y (pp_t_domain (Prop \<rightarrow>\<^sub>o Prop))"
        and Y_stock:
          "pp_t_closed_logical_stock (Prop \<rightarrow>\<^sub>o Prop) [] Y"
        and necessary:
          "\<forall>v. prefix [] v \<longrightarrow>
            pp_t_holds (Y \<acute> r) v"
        and q: "Elem q (pp_t_domain Prop)"
      obtain M where M_type:
          "[] \<turnstile> M : (Prop \<rightarrow>\<^sub>o Prop)"
        and M_logical: "pp_logical_vocabulary M"
        and YM:
          "pp_t_eqv (Prop \<rightarrow>\<^sub>o Prop) []
            Y (pp_t_closed_den M)"
        using Y_stock
        unfolding pp_t_closed_logical_stock_def by blast
      let ?X = "pp_t_closed_den M"
      have X_exact:
          "?X \<in> pp_t_exact_closed_logical_operators"
        unfolding pp_t_exact_closed_logical_operators_def
        using M_type M_logical by blast
      have X: "Elem ?X (pp_t_domain (Prop \<rightarrow>\<^sub>o Prop))"
        using pp_t_closed_den_in_domain[OF M_type] .
      have X_necessary: "\<forall>v. pp_t_holds (?X \<acute> r) v"
      proof
        fix v
        have Yr:
            "pp_t_eqv Prop v (Y \<acute> r) (?X \<acute> r)"
        proof -
          have YM_v:
              "pp_t_eqv (Prop \<rightarrow>\<^sub>o Prop) v Y ?X"
            using YM by simp
          have rr: "pp_t_eqv Prop v r r"
            using pp_t_eqv_reflexive[OF r] .
          show ?thesis
            using pp_t_app_respects[OF YM_v r r rr] .
        qed
        have Y_true: "pp_t_holds (Y \<acute> r) v"
          using necessary by simp
        show "pp_t_holds (?X \<acute> r) v"
          using pp_t_prop_eqv_at[OF Yr, of v] Y_true by simp
      qed
      have X_universal:
          "\<forall>p. Elem p (pp_t_domain Prop) \<longrightarrow>
            pp_t_holds (?X \<acute> p) []"
        using exact_recombines X_exact X_necessary by blast
      have Xq: "pp_t_holds (?X \<acute> q) []"
        using X_universal q by blast
      have qq: "pp_t_eqv Prop [] q q"
        using pp_t_eqv_reflexive[OF q] .
      have YXq:
          "pp_t_eqv Prop [] (Y \<acute> q) (?X \<acute> q)"
        using pp_t_app_respects[OF YM q q qq] .
      show "pp_t_holds (Y \<acute> q) []"
        using pp_t_prop_eqv_at[OF YXq, of "[]"] Xq by simp
    qed
  qed
qed

end

context pp_t_cone_totality
begin

sublocale ClosedLogicalNaturality:
  pp_t_closed_logical_cone_naturality
proof
  fix X
  assume "X \<in> pp_t_exact_closed_logical_operators"
  then show "pp_b_equivariant (pp_b_operator_of X)"
    by (rule pp_t_exact_closed_operator_equivariant)
qed

corollary pp_t_totality_yields_generic_seed:
  "\<exists>r. Elem r (pp_t_domain Prop) \<and>
    pp_t_unary_recombines_at
      (pp_t_closed_logical_stock (Prop \<rightarrow>\<^sub>o Prop))
      r []"
  by (rule
    ClosedLogicalNaturality.pp_t_generic_seed_recombines_closed_logical_stock_at_root)

end

interpretation UnconditionalCone: pp_t_cone_totality
proof
  fix \<sigma> s
  show "pp_t_cone_left_total \<sigma> s"
    by (rule pp_t_cone_left_total_all)
  show "pp_t_cone_right_total \<sigma> s"
    by (rule pp_t_cone_right_total_all)
qed

lemma pp_t_closed_logical_prop_den_root_truth:
  assumes typed: "[] \<turnstile> M : Prop"
    and logical: "pp_logical_vocabulary M"
  shows "pp_t_eqv Prop []
    (pp_t_closed_den M)
    (pp_zf_truth (pp_t_holds (pp_t_closed_den M) []))"
proof -
  have cone:
      "\<And>s. pp_t_cone_rel Prop s
        (pp_t_closed_den M) (pp_t_closed_den M)"
    using UnconditionalCone.pp_t_closed_logical_den_cone_related[
      OF typed logical] .
  show ?thesis
    unfolding pp_t_eqv.simps
  proof (intro allI impI)
    fix v :: "bool list"
    assume "prefix [] v"
    have cone_v:
        "\<forall>u. pp_t_holds (pp_t_closed_den M) (v @ u)
          \<longleftrightarrow> pp_t_holds (pp_t_closed_den M) u"
      using cone[of v] by simp
    have at_v:
        "pp_t_holds (pp_t_closed_den M) (v @ [])
          \<longleftrightarrow> pp_t_holds (pp_t_closed_den M) []"
      using cone_v[rule_format, of "[]"] .
    show "pp_t_holds (pp_t_closed_den M) v =
        pp_t_holds
          (pp_zf_truth (pp_t_holds (pp_t_closed_den M) [])) v"
      using at_v by simp
  qed
qed

lemma pp_t_cone_invariant_eqv_root_iff:
  assumes x: "Elem x (pp_t_domain \<sigma>)"
    and y: "Elem y (pp_t_domain \<sigma>)"
    and x_cone: "\<And>s. pp_t_cone_rel \<sigma> s x x"
    and y_cone: "\<And>s. pp_t_cone_rel \<sigma> s y y"
  shows "pp_t_eqv \<sigma> w x y \<longleftrightarrow>
    pp_t_eqv \<sigma> [] x y"
  using UnconditionalCone.pp_t_cone_rel_eqv_iff[
    OF x x y y x_cone[of w] y_cone[of w], of "[]"]
  by simp

lemma pp_t_closed_logical_stock_cone_iff:
  assumes x: "Elem x (pp_t_domain \<sigma>)"
    and y: "Elem y (pp_t_domain \<sigma>)"
    and xy: "pp_t_cone_rel \<sigma> s x y"
  shows "pp_t_closed_logical_stock \<sigma> (s @ u) x
    \<longleftrightarrow> pp_t_closed_logical_stock \<sigma> u y"
proof
  assume stock:
      "pp_t_closed_logical_stock \<sigma> (s @ u) x"
  then obtain M where typed: "[] \<turnstile> M : \<sigma>"
    and logical: "pp_logical_vocabulary M"
    and xM:
      "pp_t_eqv \<sigma> (s @ u) x (pp_t_closed_den M)"
    unfolding pp_t_closed_logical_stock_def by blast
  have den: "Elem (pp_t_closed_den M) (pp_t_domain \<sigma>)"
    using pp_t_closed_den_in_domain[OF typed] .
  have den_cone:
      "pp_t_cone_rel \<sigma> s
        (pp_t_closed_den M) (pp_t_closed_den M)"
    using UnconditionalCone.pp_t_closed_logical_den_cone_related[
      OF typed logical] .
  have yM:
      "pp_t_eqv \<sigma> u y (pp_t_closed_den M)"
    using UnconditionalCone.pp_t_cone_rel_eqv_iff[
      OF x y den den xy den_cone, of u] xM
    by blast
  show "pp_t_closed_logical_stock \<sigma> u y"
    unfolding pp_t_closed_logical_stock_def
    using y typed logical yM by blast
next
  assume stock:
      "pp_t_closed_logical_stock \<sigma> u y"
  then obtain M where typed: "[] \<turnstile> M : \<sigma>"
    and logical: "pp_logical_vocabulary M"
    and yM:
      "pp_t_eqv \<sigma> u y (pp_t_closed_den M)"
    unfolding pp_t_closed_logical_stock_def by blast
  have den: "Elem (pp_t_closed_den M) (pp_t_domain \<sigma>)"
    using pp_t_closed_den_in_domain[OF typed] .
  have den_cone:
      "pp_t_cone_rel \<sigma> s
        (pp_t_closed_den M) (pp_t_closed_den M)"
    using UnconditionalCone.pp_t_closed_logical_den_cone_related[
      OF typed logical] .
  have xM:
      "pp_t_eqv \<sigma> (s @ u) x (pp_t_closed_den M)"
    using UnconditionalCone.pp_t_cone_rel_eqv_iff[
      OF x y den den xy den_cone, of u] yM
    by blast
  show "pp_t_closed_logical_stock \<sigma> (s @ u) x"
    unfolding pp_t_closed_logical_stock_def
    using x typed logical xM by blast
qed

lemma pp_t_closed_logical_classifier_cone_related:
  "pp_t_cone_rel (\<sigma> \<rightarrow>\<^sub>o Prop) s
    (pp_t_classifier \<sigma> (pp_t_closed_logical_stock \<sigma>))
    (pp_t_classifier \<sigma> (pp_t_closed_logical_stock \<sigma>))"
  unfolding pp_t_cone_rel.simps
  by (metis pp_t_classifier_holds
      pp_t_closed_logical_stock_cone_iff)

lemma pp_t_target_classifier_membership_root_iff:
  "pp_t_closed_logical_stock
      ((Prop \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o Prop) w
      (pp_t_classifier (Prop \<rightarrow>\<^sub>o Prop)
        (pp_t_closed_logical_stock
          (Prop \<rightarrow>\<^sub>o Prop)))
    \<longleftrightarrow>
    pp_t_closed_logical_stock
      ((Prop \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o Prop) []
      (pp_t_classifier (Prop \<rightarrow>\<^sub>o Prop)
        (pp_t_closed_logical_stock
          (Prop \<rightarrow>\<^sub>o Prop)))"
proof -
  let ?U = "Prop \<rightarrow>\<^sub>o Prop"
  let ?C =
    "pp_t_classifier ?U (pp_t_closed_logical_stock ?U)"
  have C: "Elem ?C (pp_t_domain (?U \<rightarrow>\<^sub>o Prop))"
    using pp_t_classifier_in_domain[
      OF pp_t_closed_logical_stock_admissible] .
  have cone:
      "pp_t_cone_rel (?U \<rightarrow>\<^sub>o Prop) w ?C ?C"
    by (rule pp_t_closed_logical_classifier_cone_related)
  have iff:
      "pp_t_closed_logical_stock
          (?U \<rightarrow>\<^sub>o Prop) (w @ []) ?C
        \<longleftrightarrow>
        pp_t_closed_logical_stock
          (?U \<rightarrow>\<^sub>o Prop) [] ?C"
    using pp_t_closed_logical_stock_cone_iff[
      OF C C cone, of "[]"] .
  show ?thesis
    using iff by simp
qed

theorem pp_t_root_recombination_transports_to_cone:
  assumes r: "Elem r (pp_t_domain Prop)"
    and root:
      "pp_t_unary_recombines_at
        (pp_t_closed_logical_stock (Prop \<rightarrow>\<^sub>o Prop))
        r []"
  shows "pp_t_unary_recombines_at
    (pp_t_closed_logical_stock (Prop \<rightarrow>\<^sub>o Prop))
    (pp_t_cone_lift w r) w"
  unfolding pp_t_unary_recombines_at_def
proof (intro allI impI)
  fix Y q
  assume Y:
      "Elem Y (pp_t_domain (Prop \<rightarrow>\<^sub>o Prop))"
    and Y_stock:
      "pp_t_closed_logical_stock (Prop \<rightarrow>\<^sub>o Prop) w Y"
    and necessary:
      "\<forall>v. prefix w v \<longrightarrow>
        pp_t_holds (Y \<acute> pp_t_cone_lift w r) v"
    and q: "Elem q (pp_t_domain Prop)"
  let ?Z = "pp_t_cone_restrict (Prop \<rightarrow>\<^sub>o Prop) w Y"
  let ?p = "pp_t_cone_restrict Prop w q"
  have Z:
      "Elem ?Z (pp_t_domain (Prop \<rightarrow>\<^sub>o Prop))"
    using pp_t_cone_restrict_in_domain[OF Y] .
  have p: "Elem ?p (pp_t_domain Prop)"
    using pp_t_cone_restrict_in_domain[OF q] .
  have YZ:
      "pp_t_cone_rel (Prop \<rightarrow>\<^sub>o Prop) w Y ?Z"
    using pp_t_cone_restrict_related[OF Y] .
  have lift_r:
      "pp_t_cone_rel Prop w (pp_t_cone_lift w r) r"
    using pp_t_cone_extend_related[OF r, of w]
    by simp
  have qp: "pp_t_cone_rel Prop w q ?p"
    using pp_t_cone_restrict_related[OF q] .
  obtain M where M_type:
      "[] \<turnstile> M : (Prop \<rightarrow>\<^sub>o Prop)"
    and M_logical: "pp_logical_vocabulary M"
    and YM:
      "pp_t_eqv (Prop \<rightarrow>\<^sub>o Prop) w
        Y (pp_t_closed_den M)"
    using Y_stock
    unfolding pp_t_closed_logical_stock_def by blast
  let ?X = "pp_t_closed_den M"
  have X: "Elem ?X (pp_t_domain (Prop \<rightarrow>\<^sub>o Prop))"
    using pp_t_closed_den_in_domain[OF M_type] .
  have XX:
      "pp_t_cone_rel (Prop \<rightarrow>\<^sub>o Prop) w ?X ?X"
    using UnconditionalCone.pp_t_closed_logical_den_cone_related[
      OF M_type M_logical] .
  have ZX: "pp_t_eqv (Prop \<rightarrow>\<^sub>o Prop) [] ?Z ?X"
  proof -
    have iff:
        "pp_t_eqv (Prop \<rightarrow>\<^sub>o Prop) (w @ []) Y ?X
          \<longleftrightarrow>
        pp_t_eqv (Prop \<rightarrow>\<^sub>o Prop) [] ?Z ?X"
      using UnconditionalCone.pp_t_cone_rel_eqv_iff[
        OF Y Z X X YZ XX, of "[]"] .
    show ?thesis
      using iff YM by simp
  qed
  have Z_stock:
      "pp_t_closed_logical_stock (Prop \<rightarrow>\<^sub>o Prop) [] ?Z"
    unfolding pp_t_closed_logical_stock_def
    using Z M_type M_logical ZX by blast
  have Z_necessary: "\<forall>u. pp_t_holds (?Z \<acute> r) u"
  proof
    fix u
    have output_rel:
        "pp_t_cone_rel Prop w
          (Y \<acute> pp_t_cone_lift w r) (?Z \<acute> r)"
      using YZ pp_t_cone_lift_in_domain r lift_r by auto
    have left_true:
        "pp_t_holds (Y \<acute> pp_t_cone_lift w r) (w @ u)"
      using necessary by simp
    show "pp_t_holds (?Z \<acute> r) u"
      using output_rel left_true by auto
  qed
  have Z_universal:
      "\<forall>a. Elem a (pp_t_domain Prop) \<longrightarrow>
        pp_t_holds (?Z \<acute> a) []"
    using root Z Z_stock Z_necessary
    unfolding pp_t_unary_recombines_at_def by blast
  have Zp_true: "pp_t_holds (?Z \<acute> ?p) []"
    using Z_universal p by blast
  have output_rel:
      "pp_t_cone_rel Prop w (Y \<acute> q) (?Z \<acute> ?p)"
    using YZ q p qp by auto
  have output_rel_all:
      "\<forall>u. pp_t_holds (Y \<acute> q) (w @ u)
        \<longleftrightarrow> pp_t_holds (?Z \<acute> ?p) u"
    using output_rel by simp
  have at_root:
      "pp_t_holds (Y \<acute> q) (w @ [])
        \<longleftrightarrow> pp_t_holds (?Z \<acute> ?p) []"
    using output_rel_all[rule_format, of "[]"] .
  show "pp_t_holds (Y \<acute> q) w"
    using at_root Zp_true by simp
qed

theorem pp_t_generic_seed_recombines_exact_closed_logical_stock:
  "\<exists>r. Elem r (pp_t_domain Prop) \<and>
    pp_t_unary_recombines_at
      (pp_t_closed_logical_stock (Prop \<rightarrow>\<^sub>o Prop))
      r []"
  by (rule UnconditionalCone.pp_t_totality_yields_generic_seed)

definition pp_t_generic_root_seed :: ZF where
  "pp_t_generic_root_seed =
    (SOME r. Elem r (pp_t_domain Prop) \<and>
      pp_t_unary_recombines_at
        (pp_t_closed_logical_stock (Prop \<rightarrow>\<^sub>o Prop))
        r [])"

lemma pp_t_generic_root_seed_spec:
  "Elem pp_t_generic_root_seed (pp_t_domain Prop)
    \<and>
  pp_t_unary_recombines_at
    (pp_t_closed_logical_stock (Prop \<rightarrow>\<^sub>o Prop))
    pp_t_generic_root_seed []"
proof -
  have exists:
      "\<exists>r. Elem r (pp_t_domain Prop) \<and>
        pp_t_unary_recombines_at
          (pp_t_closed_logical_stock (Prop \<rightarrow>\<^sub>o Prop))
          r []"
    using pp_t_generic_seed_recombines_exact_closed_logical_stock .
  show ?thesis
    unfolding pp_t_generic_root_seed_def
    using someI_ex[OF exists] .
qed

lemma pp_t_generic_root_seed_in_domain:
  "Elem pp_t_generic_root_seed (pp_t_domain Prop)"
  using pp_t_generic_root_seed_spec by blast

lemma pp_t_generic_root_seed_recombines:
  "pp_t_unary_recombines_at
    (pp_t_closed_logical_stock (Prop \<rightarrow>\<^sub>o Prop))
    pp_t_generic_root_seed []"
  using pp_t_generic_root_seed_spec by blast

definition pp_t_generic_seed_at :: "bool list \<Rightarrow> ZF" where
  "pp_t_generic_seed_at w =
    pp_t_cone_lift w pp_t_generic_root_seed"

lemma pp_t_generic_seed_at_in_domain:
  "Elem (pp_t_generic_seed_at w) (pp_t_domain Prop)"
  unfolding pp_t_generic_seed_at_def
  by (rule pp_t_cone_lift_in_domain)

theorem pp_t_generic_seed_recombines_at_every_world:
  "pp_t_unary_recombines_at
    (pp_t_closed_logical_stock (Prop \<rightarrow>\<^sub>o Prop))
    (pp_t_generic_seed_at w) w"
  unfolding pp_t_generic_seed_at_def
  using pp_t_root_recombination_transports_to_cone[
    OF pp_t_generic_root_seed_in_domain
      pp_t_generic_root_seed_recombines] .

section \<open>The generic-seed internal interpretation\<close>

fun pp_t_generic_fundamental_at ::
    "otype \<Rightarrow> bool list \<Rightarrow> ZF \<Rightarrow> bool"
where
  "pp_t_generic_fundamental_at Ind w x = False"
| "pp_t_generic_fundamental_at Prop w x =
    pp_t_eqv Prop w x (pp_t_generic_seed_at w)"
| "pp_t_generic_fundamental_at (\<sigma> \<rightarrow>\<^sub>o \<tau>) w x =
    False"

lemma pp_t_generic_fundamental_admissible:
  "pp_t_predicate_admissible \<sigma>
    (pp_t_generic_fundamental_at \<sigma>)"
proof (cases \<sigma>)
  case Ind
  then show ?thesis
    by (simp add: pp_t_predicate_admissible_def)
next
  case Prop
  show ?thesis
    unfolding Prop pp_t_predicate_admissible_def
  proof (intro allI impI)
    fix w x y v
    assume x: "Elem x (pp_t_domain Prop)"
      and y: "Elem y (pp_t_domain Prop)"
      and xy: "pp_t_eqv Prop w x y"
      and wv: "prefix w v"
    have xy_v: "pp_t_eqv Prop v x y"
      using pp_t_eqv_persistent[OF xy wv] .
    have seed_refl:
        "pp_t_eqv Prop v
          (pp_t_generic_seed_at v) (pp_t_generic_seed_at v)"
      using pp_t_eqv_reflexive[
        OF pp_t_generic_seed_at_in_domain] .
    show "pp_t_generic_fundamental_at Prop v x =
        pp_t_generic_fundamental_at Prop v y"
      using pp_t_eqv_congruence[
        OF x y pp_t_generic_seed_at_in_domain
          pp_t_generic_seed_at_in_domain xy_v seed_refl]
      by simp
  qed
next
  case (Arr \<sigma> \<tau>)
  then show ?thesis
    by (simp add: pp_t_predicate_admissible_def)
qed

fun pp_t_generic_internal_constants ::
    "string \<Rightarrow> otype \<Rightarrow> ZF"
where
  "pp_t_generic_internal_constants c Ind = pp_t_default Ind"
| "pp_t_generic_internal_constants c Prop = pp_t_default Prop"
| "pp_t_generic_internal_constants c (\<sigma> \<rightarrow>\<^sub>o \<tau>) =
    (if c = pp_pure_name \<and> \<tau> = Prop
     then pp_t_classifier \<sigma> (pp_t_closed_logical_stock \<sigma>)
     else if c = pp_fun_name \<and> \<tau> = Prop
     then pp_t_classifier \<sigma> (pp_t_generic_fundamental_at \<sigma>)
     else pp_t_default (\<sigma> \<rightarrow>\<^sub>o \<tau>))"

lemma pp_t_generic_internal_constants_typed:
  "Elem (pp_t_generic_internal_constants c \<sigma>)
    (pp_t_domain \<sigma>)"
proof (cases \<sigma>)
  case Ind
  then show ?thesis
    using pp_t_default_in_domain[of Ind] by simp
next
  case Prop
  then show ?thesis
    using pp_t_default_in_domain[of Prop] by simp
next
  case (Arr \<sigma> \<tau>)
  have pure_classifier:
      "Elem
        (pp_t_classifier \<sigma> (pp_t_closed_logical_stock \<sigma>))
        (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o Prop))"
    using pp_t_classifier_in_domain[
      OF pp_t_closed_logical_stock_admissible] .
  have fun_classifier:
      "Elem
        (pp_t_classifier \<sigma> (pp_t_generic_fundamental_at \<sigma>))
        (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o Prop))"
    using pp_t_classifier_in_domain[
      OF pp_t_generic_fundamental_admissible] .
  have default:
      "Elem (pp_t_default (\<sigma> \<rightarrow>\<^sub>o \<tau>))
        (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    using pp_t_default_in_domain .
  show ?thesis
    using Arr pure_classifier fun_classifier default by auto
qed

interpretation GenericTreeConstants:
  pp_t_constants pp_t_generic_internal_constants
  by standard (rule pp_t_generic_internal_constants_typed)

lemma pp_t_generic_eval_Pure[simp]:
  "pp_t_eval pp_t_generic_internal_constants \<rho> (pp_Pure \<sigma>) =
    pp_t_classifier \<sigma> (pp_t_closed_logical_stock \<sigma>)"
  by (simp add: pp_Pure_def pp_pure_name_def)

lemma pp_t_generic_eval_Fun[simp]:
  "pp_t_eval pp_t_generic_internal_constants \<rho> (pp_Fun \<sigma>) =
    pp_t_classifier \<sigma> (pp_t_generic_fundamental_at \<sigma>)"
  by (simp add: pp_Fun_def pp_fun_name_def
      pp_pure_name_def)

lemma pp_t_generic_eval_pure_holds:
  assumes typed: "\<Gamma> \<turnstile> M : \<sigma>"
    and env: "pp_t_env_typed \<Gamma> \<rho>"
  shows "pp_t_holds
      (pp_t_eval pp_t_generic_internal_constants \<rho>
        (pp_pure \<sigma> M)) w
    \<longleftrightarrow>
      pp_t_closed_logical_stock \<sigma> w
        (pp_t_eval pp_t_generic_internal_constants \<rho> M)"
proof -
  have argument:
      "Elem (pp_t_eval pp_t_generic_internal_constants \<rho> M)
        (pp_t_domain \<sigma>)"
    using GenericTreeConstants.pp_t_eval_type[OF typed env]
    by (simp add: pp_t_dom_def)
  show ?thesis
    unfolding pp_pure_def
    using pp_t_classifier_holds[
      OF argument, of "pp_t_closed_logical_stock \<sigma>" w]
    by simp
qed

lemma pp_t_generic_eval_fun_holds:
  assumes typed: "\<Gamma> \<turnstile> M : \<sigma>"
    and env: "pp_t_env_typed \<Gamma> \<rho>"
  shows "pp_t_holds
      (pp_t_eval pp_t_generic_internal_constants \<rho>
        (pp_fun \<sigma> M)) w
    \<longleftrightarrow>
      pp_t_generic_fundamental_at \<sigma> w
        (pp_t_eval pp_t_generic_internal_constants \<rho> M)"
proof -
  have argument:
      "Elem (pp_t_eval pp_t_generic_internal_constants \<rho> M)
        (pp_t_domain \<sigma>)"
    using GenericTreeConstants.pp_t_eval_type[OF typed env]
    by (simp add: pp_t_dom_def)
  show ?thesis
    unfolding pp_fun_def
    using pp_t_classifier_holds[
      OF argument, of "pp_t_generic_fundamental_at \<sigma>" w]
    by simp
qed

lemma pp_t_generic_unique_fundamental_holds:
  "pp_t_holds
    (pp_t_eval pp_t_generic_internal_constants \<rho>
      (pp_unique_fundamental Prop)) w"
proof -
  let ?r = "pp_t_generic_seed_at w"
  have base: "pp_t_env_typed [] \<rho>"
    by (simp add: pp_t_env_typed_def lookup_def)
  have r_env:
      "pp_t_env_typed [Prop] (extend_env ?r \<rho>)"
    using pp_t_env_typed_extend[
      OF base pp_t_generic_seed_at_in_domain] .
  have r_is_fundamental:
      "pp_t_holds
        (pp_t_eval pp_t_generic_internal_constants
          (extend_env ?r \<rho>) (pp_fun Prop (Var 0))) w"
  proof -
    have var_type: "[Prop] \<turnstile> Var 0 : Prop"
      by simp
    have rr: "pp_t_eqv Prop w ?r ?r"
      using pp_t_eqv_reflexive[
        OF pp_t_generic_seed_at_in_domain] .
    show ?thesis
      using pp_t_generic_eval_fun_holds[
        OF var_type r_env, of w] rr
      by simp
  qed
  have uniqueness:
      "\<forall>y. Elem y (pp_t_domain Prop) \<longrightarrow>
        pp_t_holds
          (pp_t_eval pp_t_generic_internal_constants
            (extend_env y (extend_env ?r \<rho>))
            (Imp
              (pp_fun Prop (Var 0))
              (Eq Prop (Var 0) (Var 1)))) w"
  proof (intro allI impI)
    fix y
    assume y: "Elem y (pp_t_domain Prop)"
    have yr_env:
        "pp_t_env_typed [Prop, Prop]
          (extend_env y (extend_env ?r \<rho>))"
      using pp_t_env_typed_extend[OF r_env y] .
    have y_type: "[Prop, Prop] \<turnstile> Var 0 : Prop"
      by simp
    have fun_iff:
        "pp_t_holds
          (pp_t_eval pp_t_generic_internal_constants
            (extend_env y (extend_env ?r \<rho>))
            (pp_fun Prop (Var 0))) w
        \<longleftrightarrow> pp_t_eqv Prop w y ?r"
      using pp_t_generic_eval_fun_holds[
        OF y_type yr_env, of w] by simp
    have eq_iff:
        "pp_t_holds
          (pp_t_eval pp_t_generic_internal_constants
            (extend_env y (extend_env ?r \<rho>))
            (Eq Prop (Var 0) (Var 1))) w
        \<longleftrightarrow> pp_t_eqv Prop w y ?r"
      by simp
    show "pp_t_holds
        (pp_t_eval pp_t_generic_internal_constants
          (extend_env y (extend_env ?r \<rho>))
          (Imp
            (pp_fun Prop (Var 0))
            (Eq Prop (Var 0) (Var 1)))) w"
      unfolding pp_t_eval_Imp_holds
      using fun_iff eq_iff by blast
  qed
  show ?thesis
    unfolding pp_unique_fundamental_def
    apply (simp only: pp_t_eval_Exists_holds)
    apply (rule exI[of _ ?r])
    using pp_t_generic_seed_at_in_domain
      r_is_fundamental uniqueness
    by (simp only: pp_t_eval_Conj_holds
        pp_t_eval_Forall_holds)
qed

lemma pp_t_generic_no_fundamentals_holds:
  assumes nonprop: "\<sigma> \<noteq> Prop"
  shows "pp_t_holds
    (pp_t_eval pp_t_generic_internal_constants \<rho>
      (pp_no_fundamentals \<sigma>)) w"
proof -
  have base: "pp_t_env_typed [] \<rho>"
    by (simp add: pp_t_env_typed_def lookup_def)
  show ?thesis
    unfolding pp_no_fundamentals_def
    apply (simp only: pp_t_eval_Forall_holds)
    apply (intro allI impI)
  proof -
    fix x
    assume x: "Elem x (pp_t_domain \<sigma>)"
    have extended:
        "pp_t_env_typed [\<sigma>] (extend_env x \<rho>)"
      using pp_t_env_typed_extend[OF base x] .
    have var_type: "[\<sigma>] \<turnstile> Var 0 : \<sigma>"
      by simp
    have fun_false:
        "\<not> pp_t_generic_fundamental_at \<sigma> w x"
      using nonprop by (cases \<sigma>) auto
    have fun_iff:
        "pp_t_holds
          (pp_t_eval pp_t_generic_internal_constants
            (extend_env x \<rho>) (pp_fun \<sigma> (Var 0))) w
        \<longleftrightarrow> pp_t_generic_fundamental_at \<sigma> w x"
      using pp_t_generic_eval_fun_holds[
        OF var_type extended, of w] by simp
    have not_fun:
        "\<not> pp_t_holds
          (pp_t_eval pp_t_generic_internal_constants
            (extend_env x \<rho>) (pp_fun \<sigma> (Var 0))) w"
      using fun_iff fun_false by blast
    show "pp_t_holds
        (pp_t_eval pp_t_generic_internal_constants
          (extend_env x \<rho>)
          (Neg (pp_fun \<sigma> (Var 0)))) w"
      using pp_t_eval_Neg_holds[
        of pp_t_generic_internal_constants
          "extend_env x \<rho>" "pp_fun \<sigma> (Var 0)" w]
        not_fun
      by blast
  qed
qed

theorem pp_t_generic_unique_fundamental_gvalid:
  "GenericTreeConstants.TreeHenkin.gvalid \<Gamma>
    (pp_unique_fundamental Prop)"
  unfolding GenericTreeConstants.TreeHenkin.gvalid_def
    GenericTreeConstants.pp_t_den_def
  using pp_t_generic_unique_fundamental_holds by blast

theorem pp_t_generic_no_fundamentals_gvalid:
  assumes "\<sigma> \<noteq> Prop"
  shows "GenericTreeConstants.TreeHenkin.gvalid \<Gamma>
    (pp_no_fundamentals \<sigma>)"
  unfolding GenericTreeConstants.TreeHenkin.gvalid_def
    GenericTreeConstants.pp_t_den_def
  using pp_t_generic_no_fundamentals_holds[OF assms]
  by blast

theorem pp_t_generic_closed_logical_purity_gvalid:
  assumes typed: "[] \<turnstile> M : \<sigma>"
    and logical: "pp_logical_vocabulary M"
  shows "GenericTreeConstants.TreeHenkin.gvalid \<Gamma>
    (pp_pure \<sigma> M)"
proof (rule GenericTreeConstants.TreeHenkin.gvalidI)
  fix env w
  assume "env_ok (map pp_t_dom \<Gamma>) env"
  have eval_pure:
      "pp_t_holds
        (pp_t_eval pp_t_generic_internal_constants
          (pp_t_list_env env) (pp_pure \<sigma> M)) w
      \<longleftrightarrow>
        pp_t_closed_logical_stock \<sigma> w
          (pp_t_eval pp_t_generic_internal_constants
            (pp_t_list_env env) M)"
    using pp_t_generic_eval_pure_holds[
      OF typed pp_t_empty_env_typed, where w=w] .
  have stock:
      "pp_t_closed_logical_stock \<sigma> w
        (pp_t_eval pp_t_generic_internal_constants
          (pp_t_list_env env) M)"
    using pp_t_closed_logical_stock_contains_eval[
      OF typed logical] .
  show "pp_t_holds
      (GenericTreeConstants.pp_t_den
        (pp_pure \<sigma> M) env) w"
    unfolding GenericTreeConstants.pp_t_den_def
    using eval_pure stock by blast
qed

lemma pp_t_generic_closed_logical_application_closure_holds_iff:
  "pp_t_holds
      (pp_t_eval pp_t_generic_internal_constants \<rho>
        (pp_application_closure \<sigma> \<tau>)) w
    \<longleftrightarrow>
    (\<forall>f.
      Elem f (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>)) \<longrightarrow>
      (\<forall>x. Elem x (pp_t_domain \<sigma>) \<longrightarrow>
        pp_t_closed_logical_stock
          (\<sigma> \<rightarrow>\<^sub>o \<tau>) w f
        \<and> pp_t_closed_logical_stock \<sigma> w x
        \<longrightarrow>
        pp_t_closed_logical_stock \<tau> w (f \<acute> x)))"
  by (simp add: pp_application_closure_def pp_pure_def
      pp_t_classifier_holds pp_t_app_closed
      extend_env.simps)

theorem pp_t_generic_closed_logical_application_closure_gvalid:
  "GenericTreeConstants.TreeHenkin.gvalid \<Gamma>
    (pp_application_closure \<sigma> \<tau>)"
proof (rule GenericTreeConstants.TreeHenkin.gvalidI)
  fix env w
  assume "env_ok (map pp_t_dom \<Gamma>) env"
  show "pp_t_holds
      (GenericTreeConstants.pp_t_den
        (pp_application_closure \<sigma> \<tau>) env) w"
    unfolding GenericTreeConstants.pp_t_den_def
      pp_t_generic_closed_logical_application_closure_holds_iff
    using pp_t_closed_logical_stock_application_closed
    by blast
qed

lemma pp_t_generic_unary_recombination_holds_iff:
  "pp_t_holds
      (pp_t_eval pp_t_generic_internal_constants \<rho>
        pp_unary_recombination) w
    \<longleftrightarrow>
    (\<forall>X.
      Elem X (pp_t_domain (Prop \<rightarrow>\<^sub>o Prop)) \<longrightarrow>
      (\<forall>r. Elem r (pp_t_domain Prop) \<longrightarrow>
        (pp_t_closed_logical_stock
            (Prop \<rightarrow>\<^sub>o Prop) w X
          \<and> pp_t_generic_fundamental_at Prop w r)
        \<longrightarrow>
        ((\<forall>v. prefix w v \<longrightarrow>
            pp_t_holds (X \<acute> r) v)
          \<longrightarrow>
          (\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
            pp_t_holds (X \<acute> q) w))))"
  by (simp add: pp_unary_recombination_def
      pp_pure_def pp_fun_def pp_t_classifier_holds
      pp_t_prop_eqv_truth_iff pp_t_eval_ObjBox_holds
      extend_env.simps pp_t_three_extensions_index_two)

lemma pp_t_generic_fundamental_recombines:
  assumes X:
      "Elem X (pp_t_domain (Prop \<rightarrow>\<^sub>o Prop))"
    and X_stock:
      "pp_t_closed_logical_stock
        (Prop \<rightarrow>\<^sub>o Prop) w X"
    and r: "Elem r (pp_t_domain Prop)"
    and r_fundamental:
      "pp_t_generic_fundamental_at Prop w r"
    and necessary:
      "\<forall>v. prefix w v \<longrightarrow>
        pp_t_holds (X \<acute> r) v"
  shows "\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
    pp_t_holds (X \<acute> q) w"
proof -
  let ?seed = "pp_t_generic_seed_at w"
  have seed: "Elem ?seed (pp_t_domain Prop)"
    by (rule pp_t_generic_seed_at_in_domain)
  have r_seed: "pp_t_eqv Prop w r ?seed"
    using r_fundamental by simp
  have seed_necessary:
      "\<forall>v. prefix w v \<longrightarrow>
        pp_t_holds (X \<acute> ?seed) v"
  proof (intro allI impI)
    fix v
    assume wv: "prefix w v"
    have r_seed_v: "pp_t_eqv Prop v r ?seed"
      using pp_t_eqv_persistent[OF r_seed wv] .
    have applications:
        "pp_t_eqv Prop v (X \<acute> r) (X \<acute> ?seed)"
      using pp_t_arrow_member_respects[
        OF X r seed r_seed_v] .
    have r_true: "pp_t_holds (X \<acute> r) v"
      using necessary wv by blast
    show "pp_t_holds (X \<acute> ?seed) v"
      using pp_t_prop_eqv_at[OF applications, of v]
        r_true by simp
  qed
  show ?thesis
    using pp_t_generic_seed_recombines_at_every_world[
      of w] X X_stock seed_necessary
    unfolding pp_t_unary_recombines_at_def by blast
qed

theorem pp_t_generic_unary_recombination_holds:
  "pp_t_holds
    (pp_t_eval pp_t_generic_internal_constants \<rho>
      pp_unary_recombination) w"
  unfolding pp_t_generic_unary_recombination_holds_iff
  using pp_t_generic_fundamental_recombines by blast

theorem pp_t_generic_unary_recombination_gvalid:
  "GenericTreeConstants.TreeHenkin.gvalid \<Gamma>
    pp_unary_recombination"
  unfolding GenericTreeConstants.TreeHenkin.gvalid_def
    GenericTreeConstants.pp_t_den_def
  using pp_t_generic_unary_recombination_holds by blast

lemma pp_t_generic_zeroary_recombination_holds:
  "pp_t_holds
    (pp_t_eval pp_t_generic_internal_constants \<rho>
      pp_zeroary_recombination) w"
proof -
  have base: "pp_t_env_typed [] \<rho>"
    by (simp add: pp_t_env_typed_def lookup_def)
  show ?thesis
    unfolding pp_zeroary_recombination_def
    apply (simp only: pp_t_eval_Forall_holds)
    apply (intro allI impI)
  proof -
    fix P
    assume P: "Elem P (pp_t_domain Prop)"
    have extended:
        "pp_t_env_typed [Prop] (extend_env P \<rho>)"
      using pp_t_env_typed_extend[OF base P] .
    have var_type: "[Prop] \<turnstile> Var 0 : Prop"
      by simp
    have pure_iff:
        "pp_t_holds
          (pp_t_eval pp_t_generic_internal_constants
            (extend_env P \<rho>) (pp_pure Prop (Var 0))) w
        \<longleftrightarrow>
        pp_t_closed_logical_stock Prop w P"
      using pp_t_generic_eval_pure_holds[
        OF var_type extended, of w] by simp
    have modal_T:
        "pp_t_eqv Prop w P (pp_zf_truth True)
          \<Longrightarrow> pp_t_holds P w"
    proof -
      assume box: "pp_t_eqv Prop w P (pp_zf_truth True)"
      have at_w:
          "pp_t_holds P w
            \<longleftrightarrow> pp_t_holds (pp_zf_truth True) w"
        using pp_t_prop_eqv_at[OF box, of w] by simp
      show "pp_t_holds P w"
        using at_w by simp
    qed
    show "pp_t_holds
        (pp_t_eval pp_t_generic_internal_constants
          (extend_env P \<rho>)
          (Imp
            (pp_pure Prop (Var 0))
            (Imp (\<box>\<^sub>o (Var 0)) (Var 0)))) w"
      unfolding pp_t_eval_Imp_holds
      using pure_iff modal_T
      by (simp add: pp_t_eval_ObjBox_holds)
  qed
qed

theorem pp_t_generic_zeroary_recombination_gvalid:
  "GenericTreeConstants.TreeHenkin.gvalid \<Gamma>
    pp_zeroary_recombination"
  unfolding GenericTreeConstants.TreeHenkin.gvalid_def
    GenericTreeConstants.pp_t_den_def
  using pp_t_generic_zeroary_recombination_holds by blast

theorem pp_t_generic_recombination_background_gvalid:
  "GenericTreeConstants.TreeHenkin.gvalid_set
    pp_recombination_background_axioms"
  unfolding GenericTreeConstants.TreeHenkin.gvalid_set_def
proof (intro allI impI)
  fix \<Gamma> A
  assume A: "A \<in> pp_recombination_background_axioms"
  show "GenericTreeConstants.TreeHenkin.gvalid \<Gamma> A"
  proof -
    from A consider
      (purity) "A \<in> pp_purity_schema"
    | (application) "A \<in> pp_application_closure_schema"
    | (unique) "A = pp_unique_fundamental Prop"
    | (no_other) "A \<in> pp_no_other_fundamentals_schema"
    | (zeroary) "A = pp_zeroary_recombination"
    | (unary) "A = pp_unary_recombination"
      unfolding pp_recombination_background_axioms_def
        pp_background_axioms_def by blast
    then show ?thesis
    proof cases
      case purity
      then obtain \<sigma> M where typed: "[] \<turnstile> M : \<sigma>"
        and logical: "pp_logical_vocabulary M"
        and A: "A = pp_pure \<sigma> M"
        unfolding pp_purity_schema_def by blast
      show ?thesis
        unfolding A
        using pp_t_generic_closed_logical_purity_gvalid[
          OF typed logical] .
    next
      case application
      then obtain \<sigma> \<tau> where
          A: "A = pp_application_closure \<sigma> \<tau>"
        unfolding pp_application_closure_schema_def by blast
      show ?thesis
        unfolding A
        by (rule
          pp_t_generic_closed_logical_application_closure_gvalid)
    next
      case unique
      show ?thesis
        unfolding unique
        by (rule pp_t_generic_unique_fundamental_gvalid)
    next
      case no_other
      then obtain \<sigma> where nonprop: "\<sigma> \<noteq> Prop"
        and A: "A = pp_no_fundamentals \<sigma>"
        unfolding pp_no_other_fundamentals_schema_def by blast
      show ?thesis
        unfolding A
        by (rule pp_t_generic_no_fundamentals_gvalid[OF nonprop])
    next
      case zeroary
      show ?thesis
        unfolding zeroary
        by (rule pp_t_generic_zeroary_recombination_gvalid)
    next
      case unary
      show ?thesis
        unfolding unary
        by (rule pp_t_generic_unary_recombination_gvalid)
    qed
  qed
qed

lemma pp_t_generic_target_PP_holds_iff:
  "pp_t_holds
      (pp_t_eval pp_t_generic_internal_constants \<rho>
        pp_target_PP) w
    \<longleftrightarrow>
    pp_t_closed_logical_stock
      ((Prop \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o Prop) w
      (pp_t_classifier (Prop \<rightarrow>\<^sub>o Prop)
        (pp_t_closed_logical_stock
          (Prop \<rightarrow>\<^sub>o Prop)))"
proof -
  let ?U = "Prop \<rightarrow>\<^sub>o Prop"
  let ?C =
    "pp_t_classifier ?U (pp_t_closed_logical_stock ?U)"
  have C:
      "Elem ?C (pp_t_domain (?U \<rightarrow>\<^sub>o Prop))"
    using pp_t_classifier_in_domain[
      OF pp_t_closed_logical_stock_admissible] .
  show ?thesis
    unfolding pp_target_PP_def pp_purity_of_pure_def
      pp_pure_def
    using pp_t_classifier_holds[
      OF C, of
        "pp_t_closed_logical_stock (?U \<rightarrow>\<^sub>o Prop)" w]
    by simp
qed

theorem pp_t_generic_recombination_PP_gvalid_iff:
  "GenericTreeConstants.TreeHenkin.gvalid_set
      pp_recombination_PP_axioms
    \<longleftrightarrow>
    (\<forall>w.
      pp_t_closed_logical_stock
        ((Prop \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o Prop) w
        (pp_t_classifier (Prop \<rightarrow>\<^sub>o Prop)
          (pp_t_closed_logical_stock
            (Prop \<rightarrow>\<^sub>o Prop))))"
proof
  assume stock:
      "GenericTreeConstants.TreeHenkin.gvalid_set
        pp_recombination_PP_axioms"
  have target:
      "GenericTreeConstants.TreeHenkin.gvalid []
        pp_target_PP"
    using stock
    unfolding GenericTreeConstants.TreeHenkin.gvalid_set_def
      pp_recombination_PP_axioms_def
    by blast
  show "\<forall>w.
      pp_t_closed_logical_stock
        ((Prop \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o Prop) w
        (pp_t_classifier (Prop \<rightarrow>\<^sub>o Prop)
          (pp_t_closed_logical_stock
            (Prop \<rightarrow>\<^sub>o Prop)))"
  proof
    fix w
    have target_holds:
        "pp_t_holds
          (pp_t_eval pp_t_generic_internal_constants
            (pp_t_list_env []) pp_target_PP) w"
      using target
      unfolding GenericTreeConstants.TreeHenkin.gvalid_def
        GenericTreeConstants.pp_t_den_def
      by simp
    show "pp_t_closed_logical_stock
        ((Prop \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o Prop) w
        (pp_t_classifier (Prop \<rightarrow>\<^sub>o Prop)
          (pp_t_closed_logical_stock
            (Prop \<rightarrow>\<^sub>o Prop)))"
      using target_holds
      unfolding pp_t_generic_target_PP_holds_iff .
  qed
next
  assume target:
      "\<forall>w.
        pp_t_closed_logical_stock
          ((Prop \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o Prop) w
          (pp_t_classifier (Prop \<rightarrow>\<^sub>o Prop)
            (pp_t_closed_logical_stock
              (Prop \<rightarrow>\<^sub>o Prop)))"
  show "GenericTreeConstants.TreeHenkin.gvalid_set
      pp_recombination_PP_axioms"
    unfolding GenericTreeConstants.TreeHenkin.gvalid_set_def
  proof (intro allI impI)
    fix \<Gamma> A
    assume A: "A \<in> pp_recombination_PP_axioms"
    then consider
      (target) "A = pp_target_PP"
    | (background) "A \<in> pp_recombination_background_axioms"
      unfolding pp_recombination_PP_axioms_def by blast
    then show "GenericTreeConstants.TreeHenkin.gvalid \<Gamma> A"
    proof cases
      case target_case: target
      show ?thesis
        unfolding target_case
          GenericTreeConstants.TreeHenkin.gvalid_def
          GenericTreeConstants.pp_t_den_def
        using target pp_t_generic_target_PP_holds_iff
        by blast
    next
      case background
      show ?thesis
        using pp_t_generic_recombination_background_gvalid
          background
        unfolding
          GenericTreeConstants.TreeHenkin.gvalid_set_def
        by blast
    qed
  qed
qed

corollary pp_t_generic_recombination_PP_gvalid_iff_root:
  "GenericTreeConstants.TreeHenkin.gvalid_set
      pp_recombination_PP_axioms
    \<longleftrightarrow>
    pp_t_closed_logical_stock
      ((Prop \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o Prop) []
      (pp_t_classifier (Prop \<rightarrow>\<^sub>o Prop)
        (pp_t_closed_logical_stock
          (Prop \<rightarrow>\<^sub>o Prop)))"
  using pp_t_generic_recombination_PP_gvalid_iff
    pp_t_target_classifier_membership_root_iff
  by blast

end
