theory Bacon_PP_ZF_Goodman_M5_Rebuild
  imports Bacon_PP_ZF_Bacon_10_1
begin

section \<open>Goodman M5: rebuilding with a fixed logical operator\<close>

text \<open>
  This is a secondary Boolean-tree comparison construction, not a
  reconstruction of Bacon's exact appendix model.

  Goodman's final M5 step enlarges the logical vocabulary by one invariant
  unary operator and then repeats Bacon's model construction.  The point
  requiring verification is that the distinguished interpretation remains
  fixed while all nonlogical constants are glued.

  We prove the stronger type-uniform statement.  A distinguished constant
  \<open>k\<close> of a proposition-generated type \<open>\<kappa>\<close> is assigned a typed,
  cone-natural denotation \<open>K\<close> in every local model.  The rebuilt global
  interpretation assigns it literally \<open>K\<close>, glues every other constant,
  and has the required cone-view for every closed typed term in the
  proposition-generated language.
\<close>

definition pp_t_M5_fixed_glued_constants ::
    "(nat \<Rightarrow> string \<Rightarrow> otype \<Rightarrow> ZF) \<Rightarrow>
      string \<Rightarrow> otype \<Rightarrow> ZF \<Rightarrow>
      string \<Rightarrow> otype \<Rightarrow> ZF"
where
  "pp_t_M5_fixed_glued_constants A k \<kappa> K c \<sigma> =
    (if c = k \<and> \<sigma> = \<kappa>
     then K
     else pp_t_Bacon_glued_constants A c \<sigma>)"

lemma pp_t_M5_fixed_glued_constants_typed:
  assumes K_typed: "Elem K (pp_t_domain \<kappa>)"
    and family:
      "\<And>n c \<sigma>. pp_t_propositional_type \<sigma> \<Longrightarrow>
        Elem (A n c \<sigma>) (pp_t_domain \<sigma>)"
  shows "Elem
    (pp_t_M5_fixed_glued_constants A k \<kappa> K c \<sigma>)
    (pp_t_domain \<sigma>)"
proof (cases "c = k")
  case True
  show ?thesis
  proof (cases "\<sigma> = \<kappa>")
    case True
    then show ?thesis
      using \<open>c = k\<close> K_typed
      by (simp add: pp_t_M5_fixed_glued_constants_def)
  next
    case False
    have glued:
        "Elem (pp_t_Bacon_glued_constants A c \<sigma>)
          (pp_t_domain \<sigma>)"
      by (rule pp_t_Bacon_glued_constants_typed;
          rule family)
    show ?thesis
      using \<open>c = k\<close> False glued
      by (simp add: pp_t_M5_fixed_glued_constants_def)
  qed
next
  case False
  have glued:
      "Elem (pp_t_Bacon_glued_constants A c \<sigma>)
        (pp_t_domain \<sigma>)"
    by (rule pp_t_Bacon_glued_constants_typed;
        rule family)
  show ?thesis
    using False glued
    by (simp add: pp_t_M5_fixed_glued_constants_def)
qed

lemma pp_t_M5_fixed_glued_constants_distinguished:
  "pp_t_M5_fixed_glued_constants A k \<kappa> K k \<kappa> = K"
  by (simp add: pp_t_M5_fixed_glued_constants_def)

lemma pp_t_M5_fixed_glued_constants_cone:
  assumes kappa: "pp_t_propositional_type \<kappa>"
    and K_natural: "\<And>s. pp_t_cone_rel \<kappa> s K K"
    and family:
      "\<And>n c \<sigma>. pp_t_propositional_type \<sigma> \<Longrightarrow>
        Elem (A n c \<sigma>) (pp_t_domain \<sigma>)"
    and fixed: "\<And>n. A n k \<kappa> = K"
  shows "pp_t_cone_rel \<sigma> (pp_b_code n)
    (pp_t_M5_fixed_glued_constants A k \<kappa> K c \<sigma>)
    (pp_t_Bacon_completed_constants A n c \<sigma>)"
proof (cases "c = k")
  case True
  show ?thesis
  proof (cases "\<sigma> = \<kappa>")
    case True
    have local: "A n c \<sigma> = K"
      using fixed[of n] \<open>c = k\<close> True by simp
    show ?thesis
      using K_natural[of "pp_b_code n"] kappa local
        \<open>c = k\<close> True
      by (simp add: pp_t_M5_fixed_glued_constants_def
          pp_t_Bacon_completed_constants_def)
  next
    case False
    have related:
        "pp_t_cone_rel \<sigma> (pp_b_code n)
          (pp_t_Bacon_glued_constants A c \<sigma>)
          (pp_t_Bacon_completed_constants A n c \<sigma>)"
      by (rule pp_t_Bacon_glued_constants_cone;
          rule family)
    show ?thesis
      using \<open>c = k\<close> False related
      by (simp add: pp_t_M5_fixed_glued_constants_def)
  qed
next
  case False
  have related:
      "pp_t_cone_rel \<sigma> (pp_b_code n)
        (pp_t_Bacon_glued_constants A c \<sigma>)
        (pp_t_Bacon_completed_constants A n c \<sigma>)"
    by (rule pp_t_Bacon_glued_constants_cone;
        rule family)
  show ?thesis
    using False related
    by (simp add: pp_t_M5_fixed_glued_constants_def)
qed

theorem pp_t_M5_rebuild_with_fixed_logical_constant:
  assumes kappa: "pp_t_propositional_type \<kappa>"
    and K_typed: "Elem K (pp_t_domain \<kappa>)"
    and K_natural: "\<And>s. pp_t_cone_rel \<kappa> s K K"
    and family:
      "\<And>n c \<sigma>. pp_t_propositional_type \<sigma> \<Longrightarrow>
        Elem (A n c \<sigma>) (pp_t_domain \<sigma>)"
    and fixed: "\<And>n. A n k \<kappa> = K"
  shows "\<exists>C.
    (\<forall>c \<sigma>. Elem (C c \<sigma>) (pp_t_domain \<sigma>))
    \<and> C k \<kappa> = K
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
    where x = "pp_t_M5_fixed_glued_constants A k \<kappa> K"])
  show "(\<forall>c \<sigma>. Elem
          (pp_t_M5_fixed_glued_constants A k \<kappa> K c \<sigma>)
          (pp_t_domain \<sigma>))
      \<and> pp_t_M5_fixed_glued_constants A k \<kappa> K k \<kappa> = K
      \<and>
      (\<forall>n c \<sigma>. pp_t_propositional_type \<sigma> \<longrightarrow>
        pp_t_cone_rel \<sigma> (pp_b_code n)
          (pp_t_M5_fixed_glued_constants A k \<kappa> K c \<sigma>)
          (A n c \<sigma>))
      \<and>
      (\<forall>n M \<tau>.
        [] \<turnstile> M : \<tau> \<longrightarrow>
        pp_t_propositional_term M \<longrightarrow>
        pp_t_cone_rel \<tau> (pp_b_code n)
          (pp_t_eval
            (pp_t_M5_fixed_glued_constants A k \<kappa> K)
            pp_t_closed_env M)
          (pp_t_eval (A n) pp_t_closed_env M))"
  proof (intro conjI)
    show "\<forall>c \<sigma>. Elem
        (pp_t_M5_fixed_glued_constants A k \<kappa> K c \<sigma>)
        (pp_t_domain \<sigma>)"
    proof (intro allI)
      fix c \<sigma>
      show "Elem
          (pp_t_M5_fixed_glued_constants A k \<kappa> K c \<sigma>)
          (pp_t_domain \<sigma>)"
        by (rule pp_t_M5_fixed_glued_constants_typed[
              OF K_typed family])
    qed
  next
    show "pp_t_M5_fixed_glued_constants A k \<kappa> K k \<kappa> = K"
      by (rule pp_t_M5_fixed_glued_constants_distinguished)
  next
    show "\<forall>n c \<sigma>. pp_t_propositional_type \<sigma> \<longrightarrow>
        pp_t_cone_rel \<sigma> (pp_b_code n)
          (pp_t_M5_fixed_glued_constants A k \<kappa> K c \<sigma>)
          (A n c \<sigma>)"
    proof (intro allI impI)
      fix n c \<sigma>
      assume sigma: "pp_t_propositional_type \<sigma>"
      have related:
          "pp_t_cone_rel \<sigma> (pp_b_code n)
            (pp_t_M5_fixed_glued_constants A k \<kappa> K c \<sigma>)
            (pp_t_Bacon_completed_constants A n c \<sigma>)"
        by (rule pp_t_M5_fixed_glued_constants_cone[
              where A=A and k=k and \<kappa>=\<kappa> and K=K
                and n=n and c=c and \<sigma>=\<sigma>,
              OF kappa K_natural family fixed])
      show "pp_t_cone_rel \<sigma> (pp_b_code n)
          (pp_t_M5_fixed_glued_constants A k \<kappa> K c \<sigma>)
          (A n c \<sigma>)"
        using related sigma
        by (simp add: pp_t_Bacon_completed_constants_def)
    qed
  next
    show "\<forall>n M \<tau>.
        [] \<turnstile> M : \<tau> \<longrightarrow>
        pp_t_propositional_term M \<longrightarrow>
        pp_t_cone_rel \<tau> (pp_b_code n)
          (pp_t_eval
            (pp_t_M5_fixed_glued_constants A k \<kappa> K)
            pp_t_closed_env M)
          (pp_t_eval (A n) pp_t_closed_env M)"
    proof (intro allI impI)
      fix n M \<tau>
      assume typed: "[] \<turnstile> M : \<tau>"
        and fragment: "pp_t_propositional_term M"
      have global_typed:
          "\<And>c \<sigma>. Elem
            (pp_t_M5_fixed_glued_constants A k \<kappa> K c \<sigma>)
            (pp_t_domain \<sigma>)"
        by (rule pp_t_M5_fixed_glued_constants_typed[
              OF K_typed family])
      have local_typed:
          "\<And>c \<sigma>. Elem
            (pp_t_Bacon_completed_constants A n c \<sigma>)
            (pp_t_domain \<sigma>)"
        by (rule pp_t_Bacon_completed_constants_typed;
            rule family)
      have constants_related:
          "\<forall>c \<sigma>. pp_t_cone_rel \<sigma> (pp_b_code n)
            (pp_t_M5_fixed_glued_constants A k \<kappa> K c \<sigma>)
            (pp_t_Bacon_completed_constants A n c \<sigma>)"
      proof (intro allI)
        fix c \<sigma>
        show "pp_t_cone_rel \<sigma> (pp_b_code n)
            (pp_t_M5_fixed_glued_constants A k \<kappa> K c \<sigma>)
            (pp_t_Bacon_completed_constants A n c \<sigma>)"
          by (rule pp_t_M5_fixed_glued_constants_cone[
                where A=A and k=k and \<kappa>=\<kappa> and K=K
                  and n=n and c=c and \<sigma>=\<sigma>,
                OF kappa K_natural family fixed])
      qed
      have term_relation:
          "pp_t_cone_rel \<tau> (pp_b_code n)
            (pp_t_eval
              (pp_t_M5_fixed_glued_constants A k \<kappa> K)
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
          (pp_t_eval
            (pp_t_M5_fixed_glued_constants A k \<kappa> K)
            pp_t_closed_env M)
          (pp_t_eval (A n) pp_t_closed_env M)"
        using term_relation local_eval by simp
    qed
  qed
qed

corollary pp_t_M5_rebuild_with_fixed_unary_operator:
  assumes K_typed:
      "Elem K (pp_t_domain (Prop \<rightarrow>\<^sub>o Prop))"
    and K_natural:
      "\<And>s. pp_t_cone_rel (Prop \<rightarrow>\<^sub>o Prop) s K K"
    and family:
      "\<And>n c \<sigma>. pp_t_propositional_type \<sigma> \<Longrightarrow>
        Elem (A n c \<sigma>) (pp_t_domain \<sigma>)"
    and fixed:
      "\<And>n. A n k (Prop \<rightarrow>\<^sub>o Prop) = K"
  shows "\<exists>C.
    (\<forall>c \<sigma>. Elem (C c \<sigma>) (pp_t_domain \<sigma>))
    \<and> C k (Prop \<rightarrow>\<^sub>o Prop) = K
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
  using pp_t_M5_rebuild_with_fixed_logical_constant[
    of "Prop \<rightarrow>\<^sub>o Prop" K A k,
    OF _ K_typed K_natural family fixed]
  by simp

end
