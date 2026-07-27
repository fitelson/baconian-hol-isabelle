theory Bacon_PP_ZF_Bacon_10_1
  imports Bacon_PP_ZF_Tree_Generic_Seed
begin

section \<open>Bacon's Theorem 10.1: countable cone gluing\<close>

text \<open>
  Bacon states Theorem 10.1 only after restricting the type hierarchy to the
  fragment generated from proposition type.  The theorem says that a
  countable family of interpretations can be glued into one interpretation
  whose view from the nth reserved cone is the nth given interpretation.

  The following predicate records that restriction.  The individual base
  type is deliberately excluded: the tree action on individuals in the
  present frame is trivial, so arbitrary distinct individual values cannot
  be glued at different cones.
\<close>

fun pp_t_propositional_type :: "otype \<Rightarrow> bool" where
  "pp_t_propositional_type Ind = False"
| "pp_t_propositional_type Prop = True"
| "pp_t_propositional_type (\<sigma> \<rightarrow>\<^sub>o \<tau>) =
    (pp_t_propositional_type \<sigma> \<and>
     pp_t_propositional_type \<tau>)"

definition pp_t_typed_sequence ::
    "otype \<Rightarrow> (nat \<Rightarrow> ZF) \<Rightarrow> bool"
where
  "pp_t_typed_sequence \<sigma> a \<longleftrightarrow>
    (\<forall>n. Elem (a n) (pp_t_domain \<sigma>))"

text \<open>
  At proposition type this is the familiar disjoint union of supported
  lifts.  At a function type the construction is pointwise: restrict the
  global argument to each reserved cone, apply the prescribed local
  function there, and recursively glue the resulting output sequence.
\<close>

fun pp_t_branch_glue ::
    "otype \<Rightarrow> (nat \<Rightarrow> ZF) \<Rightarrow> ZF"
where
  "pp_t_branch_glue Ind a = a 0"
| "pp_t_branch_glue Prop a =
    pp_zf_of_b
      (pp_b_generic_witness (\<lambda>n. pp_b_of_zf (a n)))"
| "pp_t_branch_glue (\<sigma> \<rightarrow>\<^sub>o \<tau>) f =
    Lambda (pp_t_domain \<sigma>)
      (\<lambda>x. pp_t_branch_glue \<tau>
        (\<lambda>n. f n \<acute>
          pp_t_cone_restrict \<sigma> (pp_b_code n) x))"

text \<open>
  To prove that the recursive gluing operation respects the modalized
  function domains, we track exactly the component information visible from
  a world.  If the world lies above a reserved cone, root equivalence of that
  component suffices.  If it lies inside a reserved cone, equivalence is
  required at the corresponding local suffix.
\<close>

definition pp_t_branch_data_eqv ::
    "otype \<Rightarrow> bool list \<Rightarrow>
      (nat \<Rightarrow> ZF) \<Rightarrow> (nat \<Rightarrow> ZF) \<Rightarrow> bool"
where
  "pp_t_branch_data_eqv \<sigma> w a b \<longleftrightarrow>
    (\<forall>n. prefix w (pp_b_code n) \<longrightarrow>
      pp_t_eqv \<sigma> [] (a n) (b n))
    \<and>
    (\<forall>n u. w = pp_b_code n @ u \<longrightarrow>
      pp_t_eqv \<sigma> u (a n) (b n))"

lemma pp_t_branch_glue_Prop_in_domain:
  "Elem (pp_t_branch_glue Prop a) (pp_t_domain Prop)"
  unfolding pp_t_branch_glue.simps
  by (rule pp_zf_of_b_in_domain)

lemma pp_t_branch_glue_Prop_cone:
  assumes typed: "pp_t_typed_sequence Prop a"
  shows "pp_t_cone_rel Prop (pp_b_code n)
    (pp_t_branch_glue Prop a) (a n)"
proof -
  have component:
      "pp_b_view (pp_b_code n)
        (pp_b_generic_witness
          (\<lambda>m. pp_b_of_zf (a m))) =
       pp_b_of_zf (a n)"
    by (rule pp_b_view_generic_witness)
  show ?thesis
    using component
    unfolding pp_t_cone_rel.simps
      pp_t_branch_glue.simps
      pp_b_view_def pp_b_of_zf_def
    by auto
qed

lemma pp_t_branch_data_eqv_refl:
  assumes typed: "pp_t_typed_sequence \<sigma> a"
  shows "pp_t_branch_data_eqv \<sigma> w a a"
  unfolding pp_t_branch_data_eqv_def
  using typed pp_t_eqv_reflexive
  unfolding pp_t_typed_sequence_def by blast

text \<open>
  The proposition case of congruence is the prefix-code calculation at the
  heart of the theorem.  Every future point is either on the unused all-false
  spine, where both glued propositions are false, or lies in a unique
  reserved cone, where the appropriate component equivalence applies.
\<close>

lemma pp_t_branch_glue_Prop_congruent:
  assumes typed_a: "pp_t_typed_sequence Prop a"
    and typed_b: "pp_t_typed_sequence Prop b"
    and data: "pp_t_branch_data_eqv Prop w a b"
  shows "pp_t_eqv Prop w
    (pp_t_branch_glue Prop a) (pp_t_branch_glue Prop b)"
proof (unfold pp_t_eqv.simps, intro allI impI)
  fix v
  assume future: "prefix w v"
  show "pp_t_holds (pp_t_branch_glue Prop a) v =
      pp_t_holds (pp_t_branch_glue Prop b) v"
  proof (cases "\<exists>n u. v = pp_b_code n @ u")
    case False
    then show ?thesis
      by (simp add: pp_b_generic_witness_mem)
  next
    case True
    then obtain n u where v: "v = pp_b_code n @ u"
      by blast
    have comparable:
        "prefix w (pp_b_code n) \<or>
         prefix (pp_b_code n) w"
      using prefix_same_cases[OF future, of "pp_b_code n"]
      unfolding v prefix_def by blast
    from comparable have component:
        "pp_t_holds (a n) u = pp_t_holds (b n) u"
    proof
      assume above: "prefix w (pp_b_code n)"
      have root:
          "pp_t_eqv Prop [] (a n) (b n)"
        using data above
        unfolding pp_t_branch_data_eqv_def by blast
      show ?thesis
        using root by auto
    next
      assume inside: "prefix (pp_b_code n) w"
      then obtain t where w: "w = pp_b_code n @ t"
        unfolding prefix_def by blast
      have local:
          "pp_t_eqv Prop t (a n) (b n)"
        using data w
        unfolding pp_t_branch_data_eqv_def by blast
      have "prefix t u"
        using future w v
        by (simp add: prefix_def append_assoc)
      then show ?thesis
        using local by auto
    qed
    show ?thesis
      using component v
      by (simp add: pp_b_generic_witness_mem pp_b_of_zf_def)
  qed
qed

definition pp_t_branch_glue_invariant :: "otype \<Rightarrow> bool"
where
  "pp_t_branch_glue_invariant \<sigma> \<longleftrightarrow>
    (pp_t_propositional_type \<sigma> \<longrightarrow>
      ((\<forall>a. pp_t_typed_sequence \<sigma> a \<longrightarrow>
          Elem (pp_t_branch_glue \<sigma> a)
            (pp_t_domain \<sigma>))
       \<and>
       (\<forall>w a b.
          pp_t_typed_sequence \<sigma> a \<longrightarrow>
          pp_t_typed_sequence \<sigma> b \<longrightarrow>
          pp_t_branch_data_eqv \<sigma> w a b \<longrightarrow>
          pp_t_eqv \<sigma> w
            (pp_t_branch_glue \<sigma> a)
            (pp_t_branch_glue \<sigma> b))
       \<and>
       (\<forall>a n.
          pp_t_typed_sequence \<sigma> a \<longrightarrow>
          pp_t_cone_rel \<sigma> (pp_b_code n)
            (pp_t_branch_glue \<sigma> a) (a n))))"

lemma pp_t_cone_restrict_eqv:
  assumes x: "Elem x (pp_t_domain \<sigma>)"
    and y: "Elem y (pp_t_domain \<sigma>)"
    and xy: "pp_t_eqv \<sigma> (s @ u) x y"
  shows "pp_t_eqv \<sigma> u
    (pp_t_cone_restrict \<sigma> s x)
    (pp_t_cone_restrict \<sigma> s y)"
proof -
  have rx:
      "Elem (pp_t_cone_restrict \<sigma> s x)
        (pp_t_domain \<sigma>)"
    using pp_t_cone_restrict_in_domain[OF x] .
  have ry:
      "Elem (pp_t_cone_restrict \<sigma> s y)
        (pp_t_domain \<sigma>)"
    using pp_t_cone_restrict_in_domain[OF y] .
  have xrx:
      "pp_t_cone_rel \<sigma> s x
        (pp_t_cone_restrict \<sigma> s x)"
    using pp_t_cone_restrict_related[OF x] .
  have yry:
      "pp_t_cone_rel \<sigma> s y
        (pp_t_cone_restrict \<sigma> s y)"
    using pp_t_cone_restrict_related[OF y] .
  have iff:
      "pp_t_eqv \<sigma> (s @ u) x y
        \<longleftrightarrow>
       pp_t_eqv \<sigma> u
        (pp_t_cone_restrict \<sigma> s x)
        (pp_t_cone_restrict \<sigma> s y)"
    using UnconditionalCone.pp_t_cone_rel_eqv_iff[
      OF x rx y ry xrx yry] .
  show ?thesis
    using iff xy by blast
qed

lemma pp_t_branch_output_typed:
  assumes fseq:
      "pp_t_typed_sequence (\<sigma> \<rightarrow>\<^sub>o \<tau>) f"
    and x: "Elem x (pp_t_domain \<sigma>)"
  shows "pp_t_typed_sequence \<tau>
    (\<lambda>n. f n \<acute>
      pp_t_cone_restrict \<sigma> (pp_b_code n) x)"
  unfolding pp_t_typed_sequence_def
proof
  fix n
  have fn:
      "Elem (f n) (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    using fseq
    unfolding pp_t_typed_sequence_def by blast
  have restricted:
      "Elem (pp_t_cone_restrict \<sigma> (pp_b_code n) x)
        (pp_t_domain \<sigma>)"
    by (rule pp_t_cone_restrict_in_domain[OF x])
  show "Elem
      (f n \<acute> pp_t_cone_restrict \<sigma> (pp_b_code n) x)
      (pp_t_domain \<tau>)"
    using pp_t_app_closed[OF fn restricted] .
qed

lemma pp_t_branch_output_data_eqv:
  assumes fseq:
      "pp_t_typed_sequence (\<sigma> \<rightarrow>\<^sub>o \<tau>) f"
    and x: "Elem x (pp_t_domain \<sigma>)"
    and y: "Elem y (pp_t_domain \<sigma>)"
    and xy: "pp_t_eqv \<sigma> w x y"
  shows "pp_t_branch_data_eqv \<tau> w
    (\<lambda>n. f n \<acute>
      pp_t_cone_restrict \<sigma> (pp_b_code n) x)
    (\<lambda>n. f n \<acute>
      pp_t_cone_restrict \<sigma> (pp_b_code n) y)"
  unfolding pp_t_branch_data_eqv_def
proof
  show "\<forall>n. prefix w (pp_b_code n) \<longrightarrow>
      pp_t_eqv \<tau> []
        (f n \<acute>
          pp_t_cone_restrict \<sigma> (pp_b_code n) x)
        (f n \<acute>
          pp_t_cone_restrict \<sigma> (pp_b_code n) y)"
  proof (intro allI impI)
    fix n
    assume future: "prefix w (pp_b_code n)"
    have xy_code:
        "pp_t_eqv \<sigma> (pp_b_code n) x y"
      using pp_t_eqv_persistent[OF xy future] .
    have local:
        "pp_t_eqv \<sigma> []
          (pp_t_cone_restrict \<sigma> (pp_b_code n) x)
          (pp_t_cone_restrict \<sigma> (pp_b_code n) y)"
      using pp_t_cone_restrict_eqv[
        OF x y, of "pp_b_code n" "[]"] xy_code
      by simp
    have fn:
        "Elem (f n)
          (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
      using fseq
      unfolding pp_t_typed_sequence_def by blast
    have rx:
        "Elem (pp_t_cone_restrict \<sigma> (pp_b_code n) x)
          (pp_t_domain \<sigma>)"
      by (rule pp_t_cone_restrict_in_domain[OF x])
    have ry:
        "Elem (pp_t_cone_restrict \<sigma> (pp_b_code n) y)
          (pp_t_domain \<sigma>)"
      by (rule pp_t_cone_restrict_in_domain[OF y])
    show "pp_t_eqv \<tau> []
        (f n \<acute>
          pp_t_cone_restrict \<sigma> (pp_b_code n) x)
        (f n \<acute>
          pp_t_cone_restrict \<sigma> (pp_b_code n) y)"
      using pp_t_arrow_member_respects[
        OF fn rx ry local] .
  qed
next
  show "\<forall>n u. w = pp_b_code n @ u \<longrightarrow>
      pp_t_eqv \<tau> u
        (f n \<acute>
          pp_t_cone_restrict \<sigma> (pp_b_code n) x)
        (f n \<acute>
          pp_t_cone_restrict \<sigma> (pp_b_code n) y)"
  proof (intro allI impI)
    fix n u
    assume w: "w = pp_b_code n @ u"
    have local:
        "pp_t_eqv \<sigma> u
          (pp_t_cone_restrict \<sigma> (pp_b_code n) x)
          (pp_t_cone_restrict \<sigma> (pp_b_code n) y)"
      using pp_t_cone_restrict_eqv[
        OF x y, of "pp_b_code n" u] xy w by simp
    have fn:
        "Elem (f n)
          (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
      using fseq
      unfolding pp_t_typed_sequence_def by blast
    have rx:
        "Elem (pp_t_cone_restrict \<sigma> (pp_b_code n) x)
          (pp_t_domain \<sigma>)"
      by (rule pp_t_cone_restrict_in_domain[OF x])
    have ry:
        "Elem (pp_t_cone_restrict \<sigma> (pp_b_code n) y)
          (pp_t_domain \<sigma>)"
      by (rule pp_t_cone_restrict_in_domain[OF y])
    show "pp_t_eqv \<tau> u
        (f n \<acute>
          pp_t_cone_restrict \<sigma> (pp_b_code n) x)
        (f n \<acute>
          pp_t_cone_restrict \<sigma> (pp_b_code n) y)"
      using pp_t_arrow_member_respects[
        OF fn rx ry local] .
  qed
qed

theorem pp_t_branch_glue_invariant_all:
  "pp_t_branch_glue_invariant \<sigma>"
proof (induction \<sigma>)
  case Ind
  show ?case
    by (simp add: pp_t_branch_glue_invariant_def)
next
  case Prop
  show ?case
    unfolding pp_t_branch_glue_invariant_def
    using pp_t_branch_glue_Prop_in_domain
      pp_t_branch_glue_Prop_congruent
      pp_t_branch_glue_Prop_cone
    by blast
next
  case (Arr \<sigma> \<tau>)
  show ?case
    unfolding pp_t_branch_glue_invariant_def
  proof (intro impI)
    assume prop_arrow:
        "pp_t_propositional_type (\<sigma> \<rightarrow>\<^sub>o \<tau>)"
    have prop_sigma: "pp_t_propositional_type \<sigma>"
      and prop_tau: "pp_t_propositional_type \<tau>"
      using prop_arrow by simp_all
    have sigma_domain:
        "\<And>a. pp_t_typed_sequence \<sigma> a \<Longrightarrow>
          Elem (pp_t_branch_glue \<sigma> a)
            (pp_t_domain \<sigma>)"
      using Arr.IH(1) prop_sigma
      unfolding pp_t_branch_glue_invariant_def by blast
    have sigma_congruent:
        "\<And>w a b.
          pp_t_typed_sequence \<sigma> a \<Longrightarrow>
          pp_t_typed_sequence \<sigma> b \<Longrightarrow>
          pp_t_branch_data_eqv \<sigma> w a b \<Longrightarrow>
          pp_t_eqv \<sigma> w
            (pp_t_branch_glue \<sigma> a)
            (pp_t_branch_glue \<sigma> b)"
      using Arr.IH(1) prop_sigma
      unfolding pp_t_branch_glue_invariant_def by blast
    have sigma_cone:
        "\<And>a n. pp_t_typed_sequence \<sigma> a \<Longrightarrow>
          pp_t_cone_rel \<sigma> (pp_b_code n)
            (pp_t_branch_glue \<sigma> a) (a n)"
      using Arr.IH(1) prop_sigma
      unfolding pp_t_branch_glue_invariant_def by blast
    have tau_domain:
        "\<And>a. pp_t_typed_sequence \<tau> a \<Longrightarrow>
          Elem (pp_t_branch_glue \<tau> a)
            (pp_t_domain \<tau>)"
      using Arr.IH(2) prop_tau
      unfolding pp_t_branch_glue_invariant_def by blast
    have tau_congruent:
        "\<And>w a b.
          pp_t_typed_sequence \<tau> a \<Longrightarrow>
          pp_t_typed_sequence \<tau> b \<Longrightarrow>
          pp_t_branch_data_eqv \<tau> w a b \<Longrightarrow>
          pp_t_eqv \<tau> w
            (pp_t_branch_glue \<tau> a)
            (pp_t_branch_glue \<tau> b)"
      using Arr.IH(2) prop_tau
      unfolding pp_t_branch_glue_invariant_def by blast
    have tau_cone:
        "\<And>a n. pp_t_typed_sequence \<tau> a \<Longrightarrow>
          pp_t_cone_rel \<tau> (pp_b_code n)
            (pp_t_branch_glue \<tau> a) (a n)"
      using Arr.IH(2) prop_tau
      unfolding pp_t_branch_glue_invariant_def by blast

    let ?D =
      "\<forall>f. pp_t_typed_sequence
        (\<sigma> \<rightarrow>\<^sub>o \<tau>) f \<longrightarrow>
        Elem (pp_t_branch_glue (\<sigma> \<rightarrow>\<^sub>o \<tau>) f)
          (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    let ?C =
      "\<forall>w f g.
        pp_t_typed_sequence (\<sigma> \<rightarrow>\<^sub>o \<tau>) f \<longrightarrow>
        pp_t_typed_sequence (\<sigma> \<rightarrow>\<^sub>o \<tau>) g \<longrightarrow>
        pp_t_branch_data_eqv
          (\<sigma> \<rightarrow>\<^sub>o \<tau>) w f g \<longrightarrow>
        pp_t_eqv (\<sigma> \<rightarrow>\<^sub>o \<tau>) w
          (pp_t_branch_glue (\<sigma> \<rightarrow>\<^sub>o \<tau>) f)
          (pp_t_branch_glue (\<sigma> \<rightarrow>\<^sub>o \<tau>) g)"
    let ?R =
      "\<forall>f n.
        pp_t_typed_sequence (\<sigma> \<rightarrow>\<^sub>o \<tau>) f \<longrightarrow>
        pp_t_cone_rel (\<sigma> \<rightarrow>\<^sub>o \<tau>)
          (pp_b_code n)
          (pp_t_branch_glue (\<sigma> \<rightarrow>\<^sub>o \<tau>) f)
          (f n)"
    show "?D \<and> ?C \<and> ?R"
    proof (intro conjI)
      show "\<forall>f. pp_t_typed_sequence
        (\<sigma> \<rightarrow>\<^sub>o \<tau>) f \<longrightarrow>
      Elem (pp_t_branch_glue (\<sigma> \<rightarrow>\<^sub>o \<tau>) f)
        (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    proof (intro allI impI)
      fix f
      assume fseq:
          "pp_t_typed_sequence (\<sigma> \<rightarrow>\<^sub>o \<tau>) f"
      show "Elem
          (pp_t_branch_glue (\<sigma> \<rightarrow>\<^sub>o \<tau>) f)
          (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
        unfolding pp_t_branch_glue.simps
      proof (rule pp_t_lambda_closed)
        fix x
        assume x: "Elem x (pp_t_domain \<sigma>)"
        have outputs:
            "pp_t_typed_sequence \<tau>
              (\<lambda>n. f n \<acute>
                pp_t_cone_restrict \<sigma> (pp_b_code n) x)"
          using pp_t_branch_output_typed[OF fseq x] .
        show "Elem
            (pp_t_branch_glue \<tau>
              (\<lambda>n. f n \<acute>
                pp_t_cone_restrict \<sigma> (pp_b_code n) x))
            (pp_t_domain \<tau>)"
          using tau_domain[OF outputs] .
      next
        fix w x y
        assume x: "Elem x (pp_t_domain \<sigma>)"
          and y: "Elem y (pp_t_domain \<sigma>)"
          and xy: "pp_t_eqv \<sigma> w x y"
        have outputs_x:
            "pp_t_typed_sequence \<tau>
              (\<lambda>n. f n \<acute>
                pp_t_cone_restrict \<sigma> (pp_b_code n) x)"
          using pp_t_branch_output_typed[OF fseq x] .
        have outputs_y:
            "pp_t_typed_sequence \<tau>
              (\<lambda>n. f n \<acute>
                pp_t_cone_restrict \<sigma> (pp_b_code n) y)"
          using pp_t_branch_output_typed[OF fseq y] .
        have output_data:
            "pp_t_branch_data_eqv \<tau> w
              (\<lambda>n. f n \<acute>
                pp_t_cone_restrict \<sigma> (pp_b_code n) x)
              (\<lambda>n. f n \<acute>
                pp_t_cone_restrict \<sigma> (pp_b_code n) y)"
          using pp_t_branch_output_data_eqv[
            OF fseq x y xy] .
        show "pp_t_eqv \<tau> w
            (pp_t_branch_glue \<tau>
              (\<lambda>n. f n \<acute>
                pp_t_cone_restrict \<sigma> (pp_b_code n) x))
            (pp_t_branch_glue \<tau>
              (\<lambda>n. f n \<acute>
                pp_t_cone_restrict \<sigma> (pp_b_code n) y))"
          using tau_congruent[
            OF outputs_x outputs_y output_data] .
      qed
    qed
    next
      show "\<forall>w f g.
        pp_t_typed_sequence (\<sigma> \<rightarrow>\<^sub>o \<tau>) f \<longrightarrow>
        pp_t_typed_sequence (\<sigma> \<rightarrow>\<^sub>o \<tau>) g \<longrightarrow>
        pp_t_branch_data_eqv (\<sigma> \<rightarrow>\<^sub>o \<tau>) w f g \<longrightarrow>
        pp_t_eqv (\<sigma> \<rightarrow>\<^sub>o \<tau>) w
          (pp_t_branch_glue (\<sigma> \<rightarrow>\<^sub>o \<tau>) f)
          (pp_t_branch_glue (\<sigma> \<rightarrow>\<^sub>o \<tau>) g)"
    proof (intro allI impI)
      fix w f g
      assume functions_f:
          "pp_t_typed_sequence (\<sigma> \<rightarrow>\<^sub>o \<tau>) f"
        and functions_g:
          "pp_t_typed_sequence (\<sigma> \<rightarrow>\<^sub>o \<tau>) g"
        and data:
          "pp_t_branch_data_eqv
            (\<sigma> \<rightarrow>\<^sub>o \<tau>) w f g"
      show "pp_t_eqv (\<sigma> \<rightarrow>\<^sub>o \<tau>) w
          (pp_t_branch_glue (\<sigma> \<rightarrow>\<^sub>o \<tau>) f)
          (pp_t_branch_glue (\<sigma> \<rightarrow>\<^sub>o \<tau>) g)"
        unfolding pp_t_eqv.simps
      proof (intro allI impI)
        fix v x y
        assume future: "prefix w v"
          and x: "Elem x (pp_t_domain \<sigma>)"
          and y: "Elem y (pp_t_domain \<sigma>)"
          and xy: "pp_t_eqv \<sigma> v x y"
        have f_outputs:
            "pp_t_typed_sequence \<tau>
              (\<lambda>n. f n \<acute>
                pp_t_cone_restrict \<sigma> (pp_b_code n) x)"
          using pp_t_branch_output_typed[OF functions_f x] .
        have g_outputs:
            "pp_t_typed_sequence \<tau>
              (\<lambda>n. g n \<acute>
                pp_t_cone_restrict \<sigma> (pp_b_code n) y)"
          using pp_t_branch_output_typed[OF functions_g y] .
        have output_data:
            "pp_t_branch_data_eqv \<tau> v
              (\<lambda>n. f n \<acute>
                pp_t_cone_restrict \<sigma> (pp_b_code n) x)
              (\<lambda>n. g n \<acute>
                pp_t_cone_restrict \<sigma> (pp_b_code n) y)"
          unfolding pp_t_branch_data_eqv_def
        proof
          show "\<forall>n. prefix v (pp_b_code n) \<longrightarrow>
              pp_t_eqv \<tau> []
                (f n \<acute> pp_t_cone_restrict \<sigma>
                  (pp_b_code n) x)
                (g n \<acute> pp_t_cone_restrict \<sigma>
                  (pp_b_code n) y)"
          proof (intro allI impI)
            fix n
            assume vn: "prefix v (pp_b_code n)"
            have wn: "prefix w (pp_b_code n)"
              using prefix_order.trans[OF future vn] .
            have fg:
                "pp_t_eqv (\<sigma> \<rightarrow>\<^sub>o \<tau>) []
                  (f n) (g n)"
              using data wn
              unfolding pp_t_branch_data_eqv_def by blast
            have xy_code:
                "pp_t_eqv \<sigma> (pp_b_code n) x y"
              using pp_t_eqv_persistent[OF xy vn] .
            have local:
                "pp_t_eqv \<sigma> []
                  (pp_t_cone_restrict \<sigma> (pp_b_code n) x)
                  (pp_t_cone_restrict \<sigma> (pp_b_code n) y)"
              using pp_t_cone_restrict_eqv[
                OF x y, of "pp_b_code n" "[]"] xy_code
              by simp
            have fn:
                "Elem (f n)
                  (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
              using functions_f
              unfolding pp_t_typed_sequence_def by blast
            have gn:
                "Elem (g n)
                  (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
              using functions_g
              unfolding pp_t_typed_sequence_def by blast
            have rx:
                "Elem (pp_t_cone_restrict \<sigma>
                  (pp_b_code n) x) (pp_t_domain \<sigma>)"
              by (rule pp_t_cone_restrict_in_domain[OF x])
            have ry:
                "Elem (pp_t_cone_restrict \<sigma>
                  (pp_b_code n) y) (pp_t_domain \<sigma>)"
              by (rule pp_t_cone_restrict_in_domain[OF y])
            show "pp_t_eqv \<tau> []
                (f n \<acute> pp_t_cone_restrict \<sigma>
                  (pp_b_code n) x)
                (g n \<acute> pp_t_cone_restrict \<sigma>
                  (pp_b_code n) y)"
              using fg rx ry local by auto
          qed
        next
          show "\<forall>n u. v = pp_b_code n @ u \<longrightarrow>
              pp_t_eqv \<tau> u
                (f n \<acute> pp_t_cone_restrict \<sigma>
                  (pp_b_code n) x)
                (g n \<acute> pp_t_cone_restrict \<sigma>
                  (pp_b_code n) y)"
          proof (intro allI impI)
            fix n u
            assume v: "v = pp_b_code n @ u"
            have comparable:
                "prefix w (pp_b_code n) \<or>
                 prefix (pp_b_code n) w"
              using prefix_same_cases[OF future, of "pp_b_code n"]
              unfolding v prefix_def by blast
            from comparable have fg:
                "pp_t_eqv (\<sigma> \<rightarrow>\<^sub>o \<tau>) u
                  (f n) (g n)"
            proof
              assume above: "prefix w (pp_b_code n)"
              have root:
                  "pp_t_eqv (\<sigma> \<rightarrow>\<^sub>o \<tau>) []
                    (f n) (g n)"
                using data above
                unfolding pp_t_branch_data_eqv_def by blast
              show ?thesis
                using pp_t_eqv_persistent[OF root]
                by (simp add: prefix_def)
            next
              assume inside: "prefix (pp_b_code n) w"
              then obtain t where w:
                  "w = pp_b_code n @ t"
                unfolding prefix_def by blast
              have local:
                  "pp_t_eqv (\<sigma> \<rightarrow>\<^sub>o \<tau>) t
                    (f n) (g n)"
                using data w
                unfolding pp_t_branch_data_eqv_def by blast
              have tu: "prefix t u"
                using future w v
                by (simp add: prefix_def append_assoc)
              show ?thesis
                using pp_t_eqv_persistent[OF local tu] .
            qed
            have local:
                "pp_t_eqv \<sigma> u
                  (pp_t_cone_restrict \<sigma> (pp_b_code n) x)
                  (pp_t_cone_restrict \<sigma> (pp_b_code n) y)"
              using pp_t_cone_restrict_eqv[
                OF x y, of "pp_b_code n" u] xy v by simp
            have fn:
                "Elem (f n)
                  (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
              using functions_f
              unfolding pp_t_typed_sequence_def by blast
            have gn:
                "Elem (g n)
                  (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
              using functions_g
              unfolding pp_t_typed_sequence_def by blast
            have rx:
                "Elem (pp_t_cone_restrict \<sigma>
                  (pp_b_code n) x) (pp_t_domain \<sigma>)"
              by (rule pp_t_cone_restrict_in_domain[OF x])
            have ry:
                "Elem (pp_t_cone_restrict \<sigma>
                  (pp_b_code n) y) (pp_t_domain \<sigma>)"
              by (rule pp_t_cone_restrict_in_domain[OF y])
            show "pp_t_eqv \<tau> u
                (f n \<acute> pp_t_cone_restrict \<sigma>
                  (pp_b_code n) x)
                (g n \<acute> pp_t_cone_restrict \<sigma>
                  (pp_b_code n) y)"
              using fg rx ry local by auto
          qed
        qed
        have result: "pp_t_eqv \<tau> v
            (pp_t_branch_glue \<tau>
              (\<lambda>n. f n \<acute>
                pp_t_cone_restrict \<sigma> (pp_b_code n) x))
            (pp_t_branch_glue \<tau>
              (\<lambda>n. g n \<acute>
                pp_t_cone_restrict \<sigma> (pp_b_code n) y))"
          using tau_congruent[
            OF f_outputs g_outputs output_data] .
        show "pp_t_eqv \<tau> v
            (pp_t_branch_glue
              (\<sigma> \<rightarrow>\<^sub>o \<tau>) f \<acute> x)
            (pp_t_branch_glue
              (\<sigma> \<rightarrow>\<^sub>o \<tau>) g \<acute> y)"
          using result x y
          by (simp add: Lambda_app)
      qed
    qed
    next
      show "\<forall>f n.
        pp_t_typed_sequence (\<sigma> \<rightarrow>\<^sub>o \<tau>) f \<longrightarrow>
        pp_t_cone_rel (\<sigma> \<rightarrow>\<^sub>o \<tau>)
          (pp_b_code n)
          (pp_t_branch_glue (\<sigma> \<rightarrow>\<^sub>o \<tau>) f)
          (f n)"
    proof (intro allI impI)
      fix f n
      assume fseq:
          "pp_t_typed_sequence (\<sigma> \<rightarrow>\<^sub>o \<tau>) f"
      show "pp_t_cone_rel (\<sigma> \<rightarrow>\<^sub>o \<tau>)
          (pp_b_code n)
          (pp_t_branch_glue (\<sigma> \<rightarrow>\<^sub>o \<tau>) f)
          (f n)"
        unfolding pp_t_cone_rel.simps
      proof (intro allI impI)
        fix x y
        assume x: "Elem x (pp_t_domain \<sigma>)"
          and y: "Elem y (pp_t_domain \<sigma>)"
          and xy:
            "pp_t_cone_rel \<sigma> (pp_b_code n) x y"
        let ?rx =
          "pp_t_cone_restrict \<sigma> (pp_b_code n) x"
        let ?outputs =
          "\<lambda>m. f m \<acute>
            pp_t_cone_restrict \<sigma> (pp_b_code m) x"
        have outputs_typed:
            "pp_t_typed_sequence \<tau> ?outputs"
          using pp_t_branch_output_typed[OF fseq x] .
        have glued_cone:
            "pp_t_cone_rel \<tau> (pp_b_code n)
              (pp_t_branch_glue \<tau> ?outputs)
              (f n \<acute> ?rx)"
          using tau_cone[OF outputs_typed, of n] .
        have rx: "Elem ?rx (pp_t_domain \<sigma>)"
          by (rule pp_t_cone_restrict_in_domain[OF x])
        have xrx:
            "pp_t_cone_rel \<sigma> (pp_b_code n) x ?rx"
          by (rule pp_t_cone_restrict_related[OF x])
        have local_xy:
            "pp_t_eqv \<sigma> [] ?rx y"
        proof -
          have iff:
              "pp_t_eqv \<sigma> ((pp_b_code n) @ []) x x
                \<longleftrightarrow>
               pp_t_eqv \<sigma> [] ?rx y"
            using UnconditionalCone.pp_t_cone_rel_eqv_iff[
              OF x rx x y xrx xy] .
          have "pp_t_eqv \<sigma> (pp_b_code n) x x"
            using pp_t_eqv_reflexive[OF x] .
          then show ?thesis
            using iff by simp
        qed
        have fn:
            "Elem (f n)
              (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
          using fseq
          unfolding pp_t_typed_sequence_def by blast
        have left_output:
            "Elem (f n \<acute> ?rx) (pp_t_domain \<tau>)"
          using pp_t_app_closed[OF fn rx] .
        have right_output:
            "Elem (f n \<acute> y) (pp_t_domain \<tau>)"
          using pp_t_app_closed[OF fn y] .
        have output_eqv:
            "pp_t_eqv \<tau> [] (f n \<acute> ?rx) (f n \<acute> y)"
          using pp_t_arrow_member_respects[
            OF fn rx y local_xy] .
        have output_eqv_rev:
            "pp_t_eqv \<tau> [] (f n \<acute> y) (f n \<acute> ?rx)"
          using pp_t_eqv_symmetric[
            OF left_output right_output output_eqv] .
        have glued_domain:
            "Elem (pp_t_branch_glue \<tau> ?outputs)
              (pp_t_domain \<tau>)"
          using tau_domain[OF outputs_typed] .
        have result: "pp_t_cone_rel \<tau> (pp_b_code n)
            (pp_t_branch_glue \<tau> ?outputs)
            (f n \<acute> y)"
          using pp_t_cone_rel_replace_right[
            OF glued_domain left_output right_output
              glued_cone output_eqv_rev] .
        show "pp_t_cone_rel \<tau> (pp_b_code n)
            (pp_t_branch_glue
              (\<sigma> \<rightarrow>\<^sub>o \<tau>) f \<acute> x)
            (f n \<acute> y)"
          using result x
          by (simp add: Lambda_app)
      qed
      qed
    qed
  qed
qed

theorem pp_t_branch_glue_in_domain:
  assumes prop_type: "pp_t_propositional_type \<sigma>"
    and typed: "pp_t_typed_sequence \<sigma> a"
  shows "Elem (pp_t_branch_glue \<sigma> a)
    (pp_t_domain \<sigma>)"
  using pp_t_branch_glue_invariant_all prop_type typed
  unfolding pp_t_branch_glue_invariant_def by blast

theorem pp_t_branch_glue_cone:
  assumes prop_type: "pp_t_propositional_type \<sigma>"
    and typed: "pp_t_typed_sequence \<sigma> a"
  shows "pp_t_cone_rel \<sigma> (pp_b_code n)
    (pp_t_branch_glue \<sigma> a) (a n)"
  using pp_t_branch_glue_invariant_all prop_type typed
  unfolding pp_t_branch_glue_invariant_def by blast

theorem pp_t_Bacon_10_1_elements:
  assumes prop_type: "pp_t_propositional_type \<sigma>"
    and typed: "\<And>n. Elem (a n) (pp_t_domain \<sigma>)"
  shows "\<exists>x. Elem x (pp_t_domain \<sigma>) \<and>
    (\<forall>n. pp_t_cone_rel \<sigma> (pp_b_code n) x (a n))"
proof -
  have typed_sequence:
      "pp_t_typed_sequence \<sigma> a"
    using typed
    unfolding pp_t_typed_sequence_def by blast
  have domain:
      "Elem (pp_t_branch_glue \<sigma> a)
        (pp_t_domain \<sigma>)"
    using pp_t_branch_glue_in_domain[
      OF prop_type typed_sequence] .
  have cones:
      "\<forall>n. pp_t_cone_rel \<sigma> (pp_b_code n)
        (pp_t_branch_glue \<sigma> a) (a n)"
    using pp_t_branch_glue_cone[
      OF prop_type typed_sequence] by blast
  show ?thesis
    using domain cones by blast
qed

lemma pp_t_default_cone_self:
  "pp_t_cone_rel \<sigma> s
    (pp_t_default \<sigma>) (pp_t_default \<sigma>)"
proof (induction \<sigma> arbitrary: s)
  case Ind
  then show ?case by simp
next
  case Prop
  then show ?case
    by (simp add: pp_t_holds_def Empty)
next
  case (Arr \<sigma> \<tau>)
  show ?case
    unfolding pp_t_cone_rel.simps
  proof (intro allI impI)
    fix x y
    assume "Elem x (pp_t_domain \<sigma>)"
      and "Elem y (pp_t_domain \<sigma>)"
      and "pp_t_cone_rel \<sigma> s x y"
    show "pp_t_cone_rel \<tau> s
        (pp_t_default (\<sigma> \<rightarrow>\<^sub>o \<tau>) \<acute> x)
        (pp_t_default (\<sigma> \<rightarrow>\<^sub>o \<tau>) \<acute> y)"
      using Arr.IH(2)[of s] \<open>Elem x (pp_t_domain \<sigma>)\<close>
        \<open>Elem y (pp_t_domain \<sigma>)\<close>
      by (simp add: Lambda_app)
  qed
qed

text \<open>
  A term belongs to Bacon's proposition-generated fragment just when every
  type annotation appearing in it belongs to that fragment.  Variables need
  no separate annotation: in a closed term their binder is checked at the
  corresponding abstraction or quantifier.
\<close>

fun pp_t_propositional_term :: "oterm \<Rightarrow> bool" where
  "pp_t_propositional_term (Var n) = True"
| "pp_t_propositional_term (Const c \<sigma>) =
    pp_t_propositional_type \<sigma>"
| "pp_t_propositional_term (App M N) =
    (pp_t_propositional_term M \<and>
     pp_t_propositional_term N)"
| "pp_t_propositional_term (Lam \<sigma> M) =
    (pp_t_propositional_type \<sigma> \<and>
     pp_t_propositional_term M)"
| "pp_t_propositional_term (Eq \<sigma> M N) =
    (pp_t_propositional_type \<sigma> \<and>
     pp_t_propositional_term M \<and>
     pp_t_propositional_term N)"
| "pp_t_propositional_term (Neg A) =
    pp_t_propositional_term A"
| "pp_t_propositional_term (Conj A B) =
    (pp_t_propositional_term A \<and>
     pp_t_propositional_term B)"
| "pp_t_propositional_term (Disj A B) =
    (pp_t_propositional_term A \<and>
     pp_t_propositional_term B)"
| "pp_t_propositional_term (Imp A B) =
    (pp_t_propositional_term A \<and>
     pp_t_propositional_term B)"
| "pp_t_propositional_term (Forall \<sigma> A) =
    (pp_t_propositional_type \<sigma> \<and>
     pp_t_propositional_term A)"
| "pp_t_propositional_term (Exists \<sigma> A) =
    (pp_t_propositional_type \<sigma> \<and>
     pp_t_propositional_term A)"

definition pp_t_Bacon_completed_constants ::
    "(nat \<Rightarrow> string \<Rightarrow> otype \<Rightarrow> ZF) \<Rightarrow>
      nat \<Rightarrow> string \<Rightarrow> otype \<Rightarrow> ZF"
where
  "pp_t_Bacon_completed_constants A n c \<sigma> =
    (if pp_t_propositional_type \<sigma>
     then A n c \<sigma>
     else pp_t_default \<sigma>)"

definition pp_t_Bacon_glued_constants ::
    "(nat \<Rightarrow> string \<Rightarrow> otype \<Rightarrow> ZF) \<Rightarrow>
      string \<Rightarrow> otype \<Rightarrow> ZF"
where
  "pp_t_Bacon_glued_constants A c \<sigma> =
    (if pp_t_propositional_type \<sigma>
     then pp_t_branch_glue \<sigma> (\<lambda>n. A n c \<sigma>)
     else pp_t_default \<sigma>)"

lemma pp_t_Bacon_completed_constants_typed:
  assumes family:
      "\<And>n c \<sigma>. pp_t_propositional_type \<sigma> \<Longrightarrow>
        Elem (A n c \<sigma>) (pp_t_domain \<sigma>)"
  shows "Elem (pp_t_Bacon_completed_constants A n c \<sigma>)
    (pp_t_domain \<sigma>)"
  using family[of \<sigma> n c] pp_t_default_in_domain[of \<sigma>]
  by (simp add: pp_t_Bacon_completed_constants_def)

lemma pp_t_Bacon_glued_constants_typed:
  assumes family:
      "\<And>n c \<sigma>. pp_t_propositional_type \<sigma> \<Longrightarrow>
        Elem (A n c \<sigma>) (pp_t_domain \<sigma>)"
  shows "Elem (pp_t_Bacon_glued_constants A c \<sigma>)
    (pp_t_domain \<sigma>)"
proof (cases "pp_t_propositional_type \<sigma>")
  case True
  have typed:
      "pp_t_typed_sequence \<sigma> (\<lambda>n. A n c \<sigma>)"
    using family[OF True]
    unfolding pp_t_typed_sequence_def by blast
  show ?thesis
    using pp_t_branch_glue_in_domain[OF True typed]
    by (simp add: pp_t_Bacon_glued_constants_def True)
next
  case False
  then show ?thesis
    by (simp add: pp_t_Bacon_glued_constants_def
        pp_t_default_in_domain)
qed

lemma pp_t_Bacon_glued_constants_cone:
  assumes family:
      "\<And>n c \<sigma>. pp_t_propositional_type \<sigma> \<Longrightarrow>
        Elem (A n c \<sigma>) (pp_t_domain \<sigma>)"
  shows "pp_t_cone_rel \<sigma> (pp_b_code n)
    (pp_t_Bacon_glued_constants A c \<sigma>)
    (pp_t_Bacon_completed_constants A n c \<sigma>)"
proof (cases "pp_t_propositional_type \<sigma>")
  case True
  have typed:
      "pp_t_typed_sequence \<sigma> (\<lambda>m. A m c \<sigma>)"
    using family[OF True]
    unfolding pp_t_typed_sequence_def by blast
  show ?thesis
    using pp_t_branch_glue_cone[OF True typed, of n]
    by (simp add: pp_t_Bacon_glued_constants_def
        pp_t_Bacon_completed_constants_def True)
next
  case False
  then show ?thesis
    using pp_t_default_cone_self[of \<sigma> "pp_b_code n"]
    by (simp add: pp_t_Bacon_glued_constants_def
        pp_t_Bacon_completed_constants_def)
qed

lemma pp_t_eval_completed_constants_propositional:
  assumes fragment: "pp_t_propositional_term M"
  shows "pp_t_eval (pp_t_Bacon_completed_constants A n) \<rho> M =
    pp_t_eval (A n) \<rho> M"
  using fragment
  by (induction M arbitrary: \<rho>)
    (simp_all add: pp_t_Bacon_completed_constants_def)

context pp_t_cone_totality
begin

theorem pp_t_eval_cone_parametric_constants:
  fixes C D :: "string \<Rightarrow> otype \<Rightarrow> ZF"
  assumes C_typed: "\<And>c \<sigma>. Elem (C c \<sigma>) (pp_t_domain \<sigma>)"
    and D_typed: "\<And>c \<sigma>. Elem (D c \<sigma>) (pp_t_domain \<sigma>)"
    and typed: "\<Gamma> \<turnstile> M : \<tau>"
    and const_free:
      "\<forall>c \<sigma>. pp_t_cone_rel \<sigma> s (C c \<sigma>) (D c \<sigma>)"
    and env: "pp_t_cone_env_rel \<Gamma> s \<rho> \<eta>"
  shows "pp_t_cone_rel \<tau> s
    (pp_t_eval C \<rho> M)
    (pp_t_eval D \<eta> M)"
proof -
  interpret Left: pp_t_constants C
    by standard (rule C_typed)
  interpret Right: pp_t_constants D
    by standard (rule D_typed)
  show ?thesis
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
  have M_free: "\<forall>c \<sigma>. pp_t_cone_rel \<sigma> s (C c \<sigma>) (D c \<sigma>)"
    using App.prems(1) by simp
  have N_free: "\<forall>c \<sigma>. pp_t_cone_rel \<sigma> s (C c \<sigma>) (D c \<sigma>)"
    using App.prems(1) by simp
  have fun_rel:
      "pp_t_cone_rel (\<sigma> \<rightarrow>\<^sub>o \<tau>) s
        (pp_t_eval C \<rho> M)
        (pp_t_eval D \<eta> M)"
    using App.IH(1)[OF M_free App.prems(2)] .
  have arguments:
      "pp_t_cone_rel \<sigma> s
        (pp_t_eval C \<rho> N)
        (pp_t_eval D \<eta> N)"
    using App.IH(2)[OF N_free App.prems(2)] .
  have left_argument:
      "Elem (pp_t_eval C \<rho> N)
        (pp_t_domain \<sigma>)"
    using Left.pp_t_eval_type[
      OF App.hyps(2)
        pp_t_cone_env_rel_typed_left[OF App.prems(2)]]
    by (simp add: pp_t_dom_def)
  have right_argument:
      "Elem (pp_t_eval D \<eta> N)
        (pp_t_domain \<sigma>)"
    using Right.pp_t_eval_type[
      OF App.hyps(2)
        pp_t_cone_env_rel_typed_right[OF App.prems(2)]]
    by (simp add: pp_t_dom_def)
  show ?case
    using fun_rel left_argument right_argument arguments by simp
next
  case (Lam \<sigma> \<Gamma> M \<tau>)
  have body_free: "\<forall>c \<sigma>. pp_t_cone_rel \<sigma> s (C c \<sigma>) (D c \<sigma>)"
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
          (pp_t_eval C
            (extend_env x \<rho>) M)
          (pp_t_eval D
            (extend_env y \<eta>) M)"
      using Lam.IH[OF body_free extended] .
    show "pp_t_cone_rel \<tau> s
        ((Lambda (pp_t_domain \<sigma>)
          (\<lambda>x. pp_t_eval C
            (extend_env x \<rho>) M)) \<acute> x)
        ((Lambda (pp_t_domain \<sigma>)
          (\<lambda>y. pp_t_eval D
            (extend_env y \<eta>) M)) \<acute> y)"
      using body x y by (simp add: Lambda_app)
  qed
next
  case (Eq \<Gamma> M \<sigma> N)
  have M_free: "\<forall>c \<sigma>. pp_t_cone_rel \<sigma> s (C c \<sigma>) (D c \<sigma>)"
    using Eq.prems(1) by simp
  have N_free: "\<forall>c \<sigma>. pp_t_cone_rel \<sigma> s (C c \<sigma>) (D c \<sigma>)"
    using Eq.prems(1) by simp
  have M_rel:
      "pp_t_cone_rel \<sigma> s
        (pp_t_eval C \<rho> M)
        (pp_t_eval D \<eta> M)"
    using Eq.IH(1)[OF M_free Eq.prems(2)] .
  have N_rel:
      "pp_t_cone_rel \<sigma> s
        (pp_t_eval C \<rho> N)
        (pp_t_eval D \<eta> N)"
    using Eq.IH(2)[OF N_free Eq.prems(2)] .
  have M_left:
      "Elem (pp_t_eval C \<rho> M)
        (pp_t_domain \<sigma>)"
    using Left.pp_t_eval_type[
      OF Eq.hyps(1)
        pp_t_cone_env_rel_typed_left[OF Eq.prems(2)]]
    by (simp add: pp_t_dom_def)
  have M_right:
      "Elem (pp_t_eval D \<eta> M)
        (pp_t_domain \<sigma>)"
    using Right.pp_t_eval_type[
      OF Eq.hyps(1)
        pp_t_cone_env_rel_typed_right[OF Eq.prems(2)]]
    by (simp add: pp_t_dom_def)
  have N_left:
      "Elem (pp_t_eval C \<rho> N)
        (pp_t_domain \<sigma>)"
    using Left.pp_t_eval_type[
      OF Eq.hyps(2)
        pp_t_cone_env_rel_typed_left[OF Eq.prems(2)]]
    by (simp add: pp_t_dom_def)
  have N_right:
      "Elem (pp_t_eval D \<eta> N)
        (pp_t_domain \<sigma>)"
    using Right.pp_t_eval_type[
      OF Eq.hyps(2)
        pp_t_cone_env_rel_typed_right[OF Eq.prems(2)]]
    by (simp add: pp_t_dom_def)
  show ?case
    unfolding pp_t_cone_rel.simps
  proof (intro allI)
    fix u
    show "pp_t_holds
          (pp_t_eval C \<rho> (Eq \<sigma> M N))
          (s @ u)
        \<longleftrightarrow>
        pp_t_holds
          (pp_t_eval D \<eta> (Eq \<sigma> M N)) u"
      unfolding pp_t_eval_Eq_holds
      using pp_t_cone_rel_eqv_iff[
        OF M_left M_right N_left N_right M_rel N_rel, of u] .
  qed
next
  case (Neg \<Gamma> A)
  have A_free: "\<forall>c \<sigma>. pp_t_cone_rel \<sigma> s (C c \<sigma>) (D c \<sigma>)"
    using Neg.prems(1) by simp
  have A_rel:
      "pp_t_cone_rel Prop s
        (pp_t_eval C \<rho> A)
        (pp_t_eval D \<eta> A)"
    using Neg.IH[OF A_free Neg.prems(2)] .
  show ?case
    using A_rel by simp
next
  case (Conj \<Gamma> A B)
  have A_free: "\<forall>c \<sigma>. pp_t_cone_rel \<sigma> s (C c \<sigma>) (D c \<sigma>)"
    and B_free: "\<forall>c \<sigma>. pp_t_cone_rel \<sigma> s (C c \<sigma>) (D c \<sigma>)"
    using Conj.prems(1) by simp_all
  have A_rel:
      "pp_t_cone_rel Prop s
        (pp_t_eval C \<rho> A)
        (pp_t_eval D \<eta> A)"
    using Conj.IH(1)[OF A_free Conj.prems(2)] .
  have B_rel:
      "pp_t_cone_rel Prop s
        (pp_t_eval C \<rho> B)
        (pp_t_eval D \<eta> B)"
    using Conj.IH(2)[OF B_free Conj.prems(2)] .
  show ?case
    using A_rel B_rel by simp
next
  case (Disj \<Gamma> A B)
  have A_free: "\<forall>c \<sigma>. pp_t_cone_rel \<sigma> s (C c \<sigma>) (D c \<sigma>)"
    and B_free: "\<forall>c \<sigma>. pp_t_cone_rel \<sigma> s (C c \<sigma>) (D c \<sigma>)"
    using Disj.prems(1) by simp_all
  have A_rel:
      "pp_t_cone_rel Prop s
        (pp_t_eval C \<rho> A)
        (pp_t_eval D \<eta> A)"
    using Disj.IH(1)[OF A_free Disj.prems(2)] .
  have B_rel:
      "pp_t_cone_rel Prop s
        (pp_t_eval C \<rho> B)
        (pp_t_eval D \<eta> B)"
    using Disj.IH(2)[OF B_free Disj.prems(2)] .
  show ?case
    using A_rel B_rel by simp
next
  case (Imp \<Gamma> A B)
  have A_free: "\<forall>c \<sigma>. pp_t_cone_rel \<sigma> s (C c \<sigma>) (D c \<sigma>)"
    and B_free: "\<forall>c \<sigma>. pp_t_cone_rel \<sigma> s (C c \<sigma>) (D c \<sigma>)"
    using Imp.prems(1) by simp_all
  have A_rel:
      "pp_t_cone_rel Prop s
        (pp_t_eval C \<rho> A)
        (pp_t_eval D \<eta> A)"
    using Imp.IH(1)[OF A_free Imp.prems(2)] .
  have B_rel:
      "pp_t_cone_rel Prop s
        (pp_t_eval C \<rho> B)
        (pp_t_eval D \<eta> B)"
    using Imp.IH(2)[OF B_free Imp.prems(2)] .
  show ?case
    using A_rel B_rel by simp
next
  case (Forall \<sigma> \<Gamma> A)
  have A_free: "\<forall>c \<sigma>. pp_t_cone_rel \<sigma> s (C c \<sigma>) (D c \<sigma>)"
    using Forall.prems(1) by simp
  have body_rel:
      "\<And>x y. Elem x (pp_t_domain \<sigma>) \<Longrightarrow>
        Elem y (pp_t_domain \<sigma>) \<Longrightarrow>
        pp_t_cone_rel \<sigma> s x y \<Longrightarrow>
        pp_t_cone_rel Prop s
          (pp_t_eval C
            (extend_env x \<rho>) A)
          (pp_t_eval D
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
        (pp_t_eval C
          (extend_env x \<rho>) A)
        (pp_t_eval D
          (extend_env y \<eta>) A)"
      using Forall.IH[OF A_free extended] .
  qed
  show ?case
    unfolding pp_t_cone_rel.simps
  proof (intro allI)
    fix u
    show "pp_t_holds
          (pp_t_eval C \<rho>
            (Forall \<sigma> A)) (s @ u)
        \<longleftrightarrow>
        pp_t_holds
          (pp_t_eval D \<eta>
            (Forall \<sigma> A)) u"
      unfolding pp_t_eval_Forall_holds
    proof
      assume all_left:
          "\<forall>x. Elem x (pp_t_domain \<sigma>) \<longrightarrow>
            pp_t_holds
              (pp_t_eval C
                (extend_env x \<rho>) A) (s @ u)"
      show "\<forall>y. Elem y (pp_t_domain \<sigma>) \<longrightarrow>
          pp_t_holds
            (pp_t_eval D
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
              (pp_t_eval C
                (extend_env x \<rho>) A)
              (pp_t_eval D
                (extend_env y \<eta>) A)"
          using body_rel[OF x y xy] .
        show "pp_t_holds
            (pp_t_eval D
              (extend_env y \<eta>) A) u"
          using related all_left x by auto
      qed
    next
      assume all_right:
          "\<forall>y. Elem y (pp_t_domain \<sigma>) \<longrightarrow>
            pp_t_holds
              (pp_t_eval D
                (extend_env y \<eta>) A) u"
      show "\<forall>x. Elem x (pp_t_domain \<sigma>) \<longrightarrow>
          pp_t_holds
            (pp_t_eval C
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
              (pp_t_eval C
                (extend_env x \<rho>) A)
              (pp_t_eval D
                (extend_env y \<eta>) A)"
          using body_rel[OF x y xy] .
        show "pp_t_holds
            (pp_t_eval C
              (extend_env x \<rho>) A) (s @ u)"
          using related all_right y by auto
      qed
    qed
  qed
next
  case (Exists \<sigma> \<Gamma> A)
  have A_free: "\<forall>c \<sigma>. pp_t_cone_rel \<sigma> s (C c \<sigma>) (D c \<sigma>)"
    using Exists.prems(1) by simp
  have body_rel:
      "\<And>x y. Elem x (pp_t_domain \<sigma>) \<Longrightarrow>
        Elem y (pp_t_domain \<sigma>) \<Longrightarrow>
        pp_t_cone_rel \<sigma> s x y \<Longrightarrow>
        pp_t_cone_rel Prop s
          (pp_t_eval C
            (extend_env x \<rho>) A)
          (pp_t_eval D
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
        (pp_t_eval C
          (extend_env x \<rho>) A)
        (pp_t_eval D
          (extend_env y \<eta>) A)"
      using Exists.IH[OF A_free extended] .
  qed
  show ?case
    unfolding pp_t_cone_rel.simps
  proof (intro allI)
    fix u
    show "pp_t_holds
          (pp_t_eval C \<rho>
            (Exists \<sigma> A)) (s @ u)
        \<longleftrightarrow>
        pp_t_holds
          (pp_t_eval D \<eta>
            (Exists \<sigma> A)) u"
      unfolding pp_t_eval_Exists_holds
    proof
      assume some_left:
          "\<exists>x. Elem x (pp_t_domain \<sigma>) \<and>
            pp_t_holds
              (pp_t_eval C
                (extend_env x \<rho>) A) (s @ u)"
      then obtain x where x: "Elem x (pp_t_domain \<sigma>)"
        and true_left:
          "pp_t_holds
            (pp_t_eval C
              (extend_env x \<rho>) A) (s @ u)"
        by blast
      obtain y where y: "Elem y (pp_t_domain \<sigma>)"
        and xy: "pp_t_cone_rel \<sigma> s x y"
        using left_total[of \<sigma> s] x
        unfolding pp_t_cone_left_total_def by blast
      have related:
          "pp_t_cone_rel Prop s
            (pp_t_eval C
              (extend_env x \<rho>) A)
            (pp_t_eval D
              (extend_env y \<eta>) A)"
        using body_rel[OF x y xy] .
      have true_right:
          "pp_t_holds
            (pp_t_eval D
              (extend_env y \<eta>) A) u"
        using related true_left by auto
      show "\<exists>y. Elem y (pp_t_domain \<sigma>) \<and>
          pp_t_holds
            (pp_t_eval D
              (extend_env y \<eta>) A) u"
        using y true_right by blast
    next
      assume some_right:
          "\<exists>y. Elem y (pp_t_domain \<sigma>) \<and>
            pp_t_holds
              (pp_t_eval D
                (extend_env y \<eta>) A) u"
      then obtain y where y: "Elem y (pp_t_domain \<sigma>)"
        and true_right:
          "pp_t_holds
            (pp_t_eval D
              (extend_env y \<eta>) A) u"
        by blast
      obtain x where x: "Elem x (pp_t_domain \<sigma>)"
        and xy: "pp_t_cone_rel \<sigma> s x y"
        using right_total[of \<sigma> s] y
        unfolding pp_t_cone_right_total_def by blast
      have related:
          "pp_t_cone_rel Prop s
            (pp_t_eval C
              (extend_env x \<rho>) A)
            (pp_t_eval D
              (extend_env y \<eta>) A)"
        using body_rel[OF x y xy] .
      have true_left:
          "pp_t_holds
            (pp_t_eval C
              (extend_env x \<rho>) A) (s @ u)"
        using related true_right by auto
      show "\<exists>x. Elem x (pp_t_domain \<sigma>) \<and>
          pp_t_holds
            (pp_t_eval C
              (extend_env x \<rho>) A) (s @ u)"
        using x true_left by blast
    qed
  qed
qed
qed

end

text \<open>
  This is the model-and-term form of Bacon's Theorem 10.1.  The family
  supplies the interpretations of every constant at each index.  The
  resulting interpretation is typed, has the prescribed nth cone-view for
  every constant in the proposition-generated signature, and consequently
  has the prescribed nth cone-view for every closed typed term of that
  fragment.
\<close>

theorem pp_t_Bacon_10_1:
  assumes family:
      "\<And>n c \<sigma>. pp_t_propositional_type \<sigma> \<Longrightarrow>
        Elem (A n c \<sigma>) (pp_t_domain \<sigma>)"
  shows "\<exists>C.
    (\<forall>c \<sigma>. Elem (C c \<sigma>) (pp_t_domain \<sigma>))
    \<and>
    (\<forall>n c \<sigma>. pp_t_propositional_type \<sigma> \<longrightarrow>
      pp_t_cone_rel \<sigma> (pp_b_code n)
        (C c \<sigma>) (A n c \<sigma>))
    \<and>
    (\<forall>n M \<tau>.
      [] \<turnstile> M : \<tau> \<longrightarrow>
      pp_t_propositional_term M \<longrightarrow>
      pp_t_cone_rel \<tau> (pp_b_code n)
        (pp_t_eval C pp_t_closed_env M)
        (pp_t_eval (A n) pp_t_closed_env M))"
proof (rule exI[
    where x = "pp_t_Bacon_glued_constants A"])
  show "(\<forall>c \<sigma>.
        Elem (pp_t_Bacon_glued_constants A c \<sigma>)
          (pp_t_domain \<sigma>))
      \<and>
      (\<forall>n c \<sigma>. pp_t_propositional_type \<sigma> \<longrightarrow>
        pp_t_cone_rel \<sigma> (pp_b_code n)
          (pp_t_Bacon_glued_constants A c \<sigma>)
          (A n c \<sigma>))
      \<and>
      (\<forall>n M \<tau>.
        [] \<turnstile> M : \<tau> \<longrightarrow>
        pp_t_propositional_term M \<longrightarrow>
        pp_t_cone_rel \<tau> (pp_b_code n)
          (pp_t_eval (pp_t_Bacon_glued_constants A)
            pp_t_closed_env M)
          (pp_t_eval (A n) pp_t_closed_env M))"
  proof (intro conjI)
    show "\<forall>c \<sigma>.
        Elem (pp_t_Bacon_glued_constants A c \<sigma>)
          (pp_t_domain \<sigma>)"
    proof (intro allI)
      fix c \<sigma>
      show "Elem (pp_t_Bacon_glued_constants A c \<sigma>)
          (pp_t_domain \<sigma>)"
        by (rule pp_t_Bacon_glued_constants_typed;
            rule family)
    qed
  next
    show "\<forall>n c \<sigma>. pp_t_propositional_type \<sigma> \<longrightarrow>
        pp_t_cone_rel \<sigma> (pp_b_code n)
          (pp_t_Bacon_glued_constants A c \<sigma>)
          (A n c \<sigma>)"
    proof (intro allI impI)
      fix n c \<sigma>
      assume fragment: "pp_t_propositional_type \<sigma>"
      have related:
          "pp_t_cone_rel \<sigma> (pp_b_code n)
            (pp_t_Bacon_glued_constants A c \<sigma>)
            (pp_t_Bacon_completed_constants A n c \<sigma>)"
        by (rule pp_t_Bacon_glued_constants_cone;
            rule family)
      show "pp_t_cone_rel \<sigma> (pp_b_code n)
          (pp_t_Bacon_glued_constants A c \<sigma>)
          (A n c \<sigma>)"
        using related fragment
        by (simp add: pp_t_Bacon_completed_constants_def)
    qed
  next
    show "\<forall>n M \<tau>.
        [] \<turnstile> M : \<tau> \<longrightarrow>
        pp_t_propositional_term M \<longrightarrow>
        pp_t_cone_rel \<tau> (pp_b_code n)
          (pp_t_eval (pp_t_Bacon_glued_constants A)
            pp_t_closed_env M)
          (pp_t_eval (A n) pp_t_closed_env M)"
    proof (intro allI impI)
      fix n M \<tau>
      assume typed: "[] \<turnstile> M : \<tau>"
        and fragment: "pp_t_propositional_term M"
      have global_typed:
          "\<And>c \<sigma>. Elem
            (pp_t_Bacon_glued_constants A c \<sigma>)
            (pp_t_domain \<sigma>)"
        by (rule pp_t_Bacon_glued_constants_typed;
            rule family)
      have local_typed:
          "\<And>c \<sigma>. Elem
            (pp_t_Bacon_completed_constants A n c \<sigma>)
            (pp_t_domain \<sigma>)"
        by (rule pp_t_Bacon_completed_constants_typed;
            rule family)
      have constants_related:
          "\<forall>c \<sigma>. pp_t_cone_rel \<sigma> (pp_b_code n)
            (pp_t_Bacon_glued_constants A c \<sigma>)
            (pp_t_Bacon_completed_constants A n c \<sigma>)"
      proof (intro allI)
        fix c \<sigma>
        show "pp_t_cone_rel \<sigma> (pp_b_code n)
            (pp_t_Bacon_glued_constants A c \<sigma>)
            (pp_t_Bacon_completed_constants A n c \<sigma>)"
          by (rule pp_t_Bacon_glued_constants_cone;
              rule family)
      qed
      have term_relation:
          "pp_t_cone_rel \<tau> (pp_b_code n)
            (pp_t_eval (pp_t_Bacon_glued_constants A)
              pp_t_closed_env M)
            (pp_t_eval
              (pp_t_Bacon_completed_constants A n)
              pp_t_closed_env M)"
        using UnconditionalCone.pp_t_eval_cone_parametric_constants[
          OF global_typed local_typed typed constants_related
            UnconditionalCone.pp_t_closed_env_cone_related] .
      have local_eval:
          "pp_t_eval (pp_t_Bacon_completed_constants A n)
              pp_t_closed_env M =
            pp_t_eval (A n) pp_t_closed_env M"
        using pp_t_eval_completed_constants_propositional[
          OF fragment] .
      show "pp_t_cone_rel \<tau> (pp_b_code n)
          (pp_t_eval (pp_t_Bacon_glued_constants A)
            pp_t_closed_env M)
          (pp_t_eval (A n) pp_t_closed_env M)"
        using term_relation local_eval by simp
    qed
  qed
qed

text \<open>
  The restriction to the proposition-generated hierarchy is necessary for
  this frame.  Its action at individual type is trivial, so a single global
  individual can have prescribed cone-views only when all prescriptions are
  equal.
\<close>

theorem pp_t_Bacon_10_1_Ind_requires_constant_family:
  assumes glue:
      "\<And>k. pp_t_cone_rel Ind (pp_b_code k) x (a k)"
  shows "a m = a n"
  using glue[of m] glue[of n] by simp

corollary pp_t_Bacon_10_1_Ind_distinct_family_impossible:
  assumes distinct: "a m \<noteq> a n"
  shows "\<not> (\<exists>x. \<forall>k.
    pp_t_cone_rel Ind (pp_b_code k) x (a k))"
proof
  assume "\<exists>x. \<forall>k.
      pp_t_cone_rel Ind (pp_b_code k) x (a k)"
  then obtain x where glue:
      "\<And>k. pp_t_cone_rel Ind (pp_b_code k) x (a k)"
    by blast
  have "a m = a n"
    using pp_t_Bacon_10_1_Ind_requires_constant_family[
      OF glue] .
  then show False
    using distinct by contradiction
qed

end
