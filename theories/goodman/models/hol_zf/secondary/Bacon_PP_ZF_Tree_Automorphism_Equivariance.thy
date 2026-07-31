theory Bacon_PP_ZF_Tree_Automorphism_Equivariance
  imports Bacon_PP_ZF_Tree_Logical_Stock
begin

section \<open>Equivariance under the root-child interchange\<close>

text \<open>
  The rooted Boolean tree has an involution which interchanges the two
  immediate subtrees and leaves every later letter unchanged.  We lift that
  involution through the complete type hierarchy.  At arrow types the lift is
  conjugation; this is what permits the full higher-order quantifiers to be
  reindexed by the induced bijections of their domains.
\<close>

fun pp_t_root_swap :: "bool list \<Rightarrow> bool list" where
  "pp_t_root_swap [] = []"
| "pp_t_root_swap (b # w) = (\<not> b) # w"

lemma pp_t_root_swap_involution[simp]:
  "pp_t_root_swap (pp_t_root_swap w) = w"
  by (cases w) simp_all

lemma pp_t_root_swap_prefix_iff[simp]:
  "prefix (pp_t_root_swap u) (pp_t_root_swap v)
    \<longleftrightarrow> prefix u v"
  by (cases u; cases v; auto simp: prefix_def)

fun pp_t_aut :: "otype \<Rightarrow> ZF \<Rightarrow> ZF" where
  "pp_t_aut Ind x = x"
| "pp_t_aut Prop P =
    pp_t_prop (\<lambda>w. pp_t_holds P (pp_t_root_swap w))"
| "pp_t_aut (\<sigma> \<rightarrow>\<^sub>o \<tau>) f =
    Lambda (pp_t_domain \<sigma>)
      (\<lambda>x. pp_t_aut \<tau> (f \<acute> pp_t_aut \<sigma> x))"

lemma pp_t_aut_apply:
  assumes x: "Elem x (pp_t_domain \<sigma>)"
  shows "pp_t_aut (\<sigma> \<rightarrow>\<^sub>o \<tau>) f \<acute> x =
    pp_t_aut \<tau> (f \<acute> pp_t_aut \<sigma> x)"
  using x by (simp add: Lambda_app)

theorem pp_t_aut_type_package:
  "(\<forall>x. Elem x (pp_t_domain \<sigma>)
      \<longrightarrow> Elem (pp_t_aut \<sigma> x) (pp_t_domain \<sigma>))
   \<and>
   (\<forall>x. Elem x (pp_t_domain \<sigma>)
      \<longrightarrow> pp_t_aut \<sigma> (pp_t_aut \<sigma> x) = x)
   \<and>
   (\<forall>w x y.
      Elem x (pp_t_domain \<sigma>)
      \<longrightarrow> Elem y (pp_t_domain \<sigma>)
      \<longrightarrow>
      (pp_t_eqv \<sigma> w
          (pp_t_aut \<sigma> x) (pp_t_aut \<sigma> y)
        \<longleftrightarrow>
       pp_t_eqv \<sigma> (pp_t_root_swap w) x y))"
proof (induction \<sigma>)
  case Ind
  then show ?case by simp
next
  case Prop
  have domain:
      "\<And>P. Elem P (pp_t_domain Prop) \<Longrightarrow>
        Elem (pp_t_aut Prop P) (pp_t_domain Prop)"
    using pp_t_prop_in_domain by simp
  have involution:
      "\<And>P. Elem P (pp_t_domain Prop) \<Longrightarrow>
        pp_t_aut Prop (pp_t_aut Prop P) = P"
  proof -
    fix P
    assume P: "Elem P (pp_t_domain Prop)"
    show "pp_t_aut Prop (pp_t_aut Prop P) = P"
    proof (rule pp_t_prop_ext)
      show "Elem (pp_t_aut Prop (pp_t_aut Prop P))
          (pp_t_domain Prop)"
        unfolding pp_t_aut.simps
        by (rule pp_t_prop_in_domain)
      show "Elem P (pp_t_domain Prop)" by (rule P)
      fix w
      show "pp_t_holds (pp_t_aut Prop (pp_t_aut Prop P)) w
          \<longleftrightarrow> pp_t_holds P w"
        by simp
    qed
  qed
  have equivariance:
      "\<And>w P Q.
        Elem P (pp_t_domain Prop) \<Longrightarrow>
        Elem Q (pp_t_domain Prop) \<Longrightarrow>
        (pp_t_eqv Prop w
            (pp_t_aut Prop P) (pp_t_aut Prop Q)
          \<longleftrightarrow>
         pp_t_eqv Prop (pp_t_root_swap w) P Q)"
  proof -
    fix w P Q
    assume P: "Elem P (pp_t_domain Prop)"
      and Q: "Elem Q (pp_t_domain Prop)"
    show "pp_t_eqv Prop w
          (pp_t_aut Prop P) (pp_t_aut Prop Q)
        \<longleftrightarrow>
        pp_t_eqv Prop (pp_t_root_swap w) P Q"
    proof (rule iffI)
      assume left:
          "pp_t_eqv Prop w
            (pp_t_aut Prop P) (pp_t_aut Prop Q)"
      show "pp_t_eqv Prop (pp_t_root_swap w) P Q"
      unfolding pp_t_eqv.simps
      proof (intro allI impI)
        fix v
        assume future: "prefix (pp_t_root_swap w) v"
        have swapped_future:
            "prefix w (pp_t_root_swap v)"
          using future
          by (metis pp_t_root_swap_involution
              pp_t_root_swap_prefix_iff)
        have at_swapped:
            "pp_t_holds (pp_t_aut Prop P)
                (pp_t_root_swap v)
              \<longleftrightarrow>
             pp_t_holds (pp_t_aut Prop Q)
                (pp_t_root_swap v)"
          using pp_t_prop_eqv_at[OF left swapped_future] .
        show "pp_t_holds P v = pp_t_holds Q v"
          using at_swapped by simp
      qed
    next
      assume right:
          "pp_t_eqv Prop (pp_t_root_swap w) P Q"
      show "pp_t_eqv Prop w
          (pp_t_aut Prop P) (pp_t_aut Prop Q)"
      unfolding pp_t_eqv.simps
      proof (intro allI impI)
        fix v
        assume future: "prefix w v"
        have swapped_future:
            "prefix (pp_t_root_swap w) (pp_t_root_swap v)"
          using future by simp
        have at_swapped:
            "pp_t_holds P (pp_t_root_swap v)
              \<longleftrightarrow>
             pp_t_holds Q (pp_t_root_swap v)"
          using right swapped_future by simp
        show "pp_t_holds (pp_t_aut Prop P) v =
            pp_t_holds (pp_t_aut Prop Q) v"
          using at_swapped by simp
      qed
    qed
  qed
  show ?case
    using domain involution equivariance by blast
next
  case (Arr \<sigma> \<tau>)
  have sigma_domain:
      "\<And>x. Elem x (pp_t_domain \<sigma>) \<Longrightarrow>
        Elem (pp_t_aut \<sigma> x) (pp_t_domain \<sigma>)"
    using Arr.IH by blast
  have tau_domain:
      "\<And>x. Elem x (pp_t_domain \<tau>) \<Longrightarrow>
        Elem (pp_t_aut \<tau> x) (pp_t_domain \<tau>)"
    using Arr.IH by blast
  have sigma_involution:
      "\<And>x. Elem x (pp_t_domain \<sigma>) \<Longrightarrow>
        pp_t_aut \<sigma> (pp_t_aut \<sigma> x) = x"
    using Arr.IH by blast
  have tau_involution:
      "\<And>x. Elem x (pp_t_domain \<tau>) \<Longrightarrow>
        pp_t_aut \<tau> (pp_t_aut \<tau> x) = x"
    using Arr.IH by blast
  have sigma_equivariance:
      "\<And>w x y.
        Elem x (pp_t_domain \<sigma>) \<Longrightarrow>
        Elem y (pp_t_domain \<sigma>) \<Longrightarrow>
        (pp_t_eqv \<sigma> w
            (pp_t_aut \<sigma> x) (pp_t_aut \<sigma> y)
          \<longleftrightarrow>
         pp_t_eqv \<sigma> (pp_t_root_swap w) x y)"
    using Arr.IH by blast
  have tau_equivariance:
      "\<And>w x y.
        Elem x (pp_t_domain \<tau>) \<Longrightarrow>
        Elem y (pp_t_domain \<tau>) \<Longrightarrow>
        (pp_t_eqv \<tau> w
            (pp_t_aut \<tau> x) (pp_t_aut \<tau> y)
          \<longleftrightarrow>
         pp_t_eqv \<tau> (pp_t_root_swap w) x y)"
    using Arr.IH by blast

  have domain:
      "\<And>f. Elem f (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))
        \<Longrightarrow>
        Elem (pp_t_aut (\<sigma> \<rightarrow>\<^sub>o \<tau>) f)
          (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
  proof -
    fix f
    assume f: "Elem f (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    show "Elem (pp_t_aut (\<sigma> \<rightarrow>\<^sub>o \<tau>) f)
        (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
      unfolding pp_t_aut.simps
    proof (rule pp_t_lambda_closed)
      fix x
      assume x: "Elem x (pp_t_domain \<sigma>)"
      have ax: "Elem (pp_t_aut \<sigma> x) (pp_t_domain \<sigma>)"
        using sigma_domain[OF x] .
      have fx:
          "Elem (f \<acute> pp_t_aut \<sigma> x) (pp_t_domain \<tau>)"
        using pp_t_app_closed[OF f ax] .
      show "Elem (pp_t_aut \<tau> (f \<acute> pp_t_aut \<sigma> x))
          (pp_t_domain \<tau>)"
        using tau_domain[OF fx] .
    next
      fix w x y
      assume x: "Elem x (pp_t_domain \<sigma>)"
        and y: "Elem y (pp_t_domain \<sigma>)"
        and xy: "pp_t_eqv \<sigma> w x y"
      have ax: "Elem (pp_t_aut \<sigma> x) (pp_t_domain \<sigma>)"
        using sigma_domain[OF x] .
      have ay: "Elem (pp_t_aut \<sigma> y) (pp_t_domain \<sigma>)"
        using sigma_domain[OF y] .
      have axy:
          "pp_t_eqv \<sigma> (pp_t_root_swap w)
            (pp_t_aut \<sigma> x) (pp_t_aut \<sigma> y)"
        using sigma_equivariance[OF x y, of "pp_t_root_swap w"] xy
        by simp
      have fxy:
          "pp_t_eqv \<tau> (pp_t_root_swap w)
            (f \<acute> pp_t_aut \<sigma> x)
            (f \<acute> pp_t_aut \<sigma> y)"
        using pp_t_arrow_member_respects[OF f ax ay axy] .
      have fx:
          "Elem (f \<acute> pp_t_aut \<sigma> x) (pp_t_domain \<tau>)"
        using pp_t_app_closed[OF f ax] .
      have fy:
          "Elem (f \<acute> pp_t_aut \<sigma> y) (pp_t_domain \<tau>)"
        using pp_t_app_closed[OF f ay] .
      show "pp_t_eqv \<tau> w
          (pp_t_aut \<tau> (f \<acute> pp_t_aut \<sigma> x))
          (pp_t_aut \<tau> (f \<acute> pp_t_aut \<sigma> y))"
        using tau_equivariance[OF fx fy, of w] fxy by blast
    qed
  qed

  have involution:
      "\<And>f. Elem f (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))
        \<Longrightarrow>
        pp_t_aut (\<sigma> \<rightarrow>\<^sub>o \<tau>)
          (pp_t_aut (\<sigma> \<rightarrow>\<^sub>o \<tau>) f) = f"
  proof -
    fix f
    assume f: "Elem f (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    have af:
        "Elem (pp_t_aut (\<sigma> \<rightarrow>\<^sub>o \<tau>) f)
          (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
      using domain[OF f] .
    have f_fun:
        "Elem f (Fun (pp_t_domain \<sigma>) (pp_t_domain \<tau>))"
      using pp_t_arrow_member_function[OF f] .
    obtain F where f_rep:
        "f = Lambda (pp_t_domain \<sigma>) F"
      using Elem_Fun_Lambda[OF f_fun] by blast
    have pointwise:
        "\<forall>x. Elem x (pp_t_domain \<sigma>) \<longrightarrow>
          pp_t_aut \<tau>
            (pp_t_aut (\<sigma> \<rightarrow>\<^sub>o \<tau>) f
              \<acute> pp_t_aut \<sigma> x)
          = F x"
    proof (intro allI impI)
      fix x
      assume x: "Elem x (pp_t_domain \<sigma>)"
      have ax: "Elem (pp_t_aut \<sigma> x) (pp_t_domain \<sigma>)"
        using sigma_domain[OF x] .
      have aax: "pp_t_aut \<sigma> (pp_t_aut \<sigma> x) = x"
        using sigma_involution[OF x] .
      have fx: "Elem (f \<acute> x) (pp_t_domain \<tau>)"
        using pp_t_app_closed[OF f x] .
      have inner:
          "pp_t_aut (\<sigma> \<rightarrow>\<^sub>o \<tau>) f
              \<acute> pp_t_aut \<sigma> x
            = pp_t_aut \<tau>
                (f \<acute> pp_t_aut \<sigma> (pp_t_aut \<sigma> x))"
        using pp_t_aut_apply[OF ax] .
      show "pp_t_aut \<tau>
            (pp_t_aut (\<sigma> \<rightarrow>\<^sub>o \<tau>) f
              \<acute> pp_t_aut \<sigma> x)
          = F x"
        using inner aax tau_involution[OF fx] f_rep x
        by (simp add: Lambda_app)
    qed
    show "pp_t_aut (\<sigma> \<rightarrow>\<^sub>o \<tau>)
        (pp_t_aut (\<sigma> \<rightarrow>\<^sub>o \<tau>) f) = f"
      unfolding pp_t_aut.simps f_rep
      using pointwise f_rep by (simp add: Lambda_ext)
  qed

  have equivariance:
      "\<And>w f g.
        Elem f (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>)) \<Longrightarrow>
        Elem g (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>)) \<Longrightarrow>
        (pp_t_eqv (\<sigma> \<rightarrow>\<^sub>o \<tau>) w
            (pp_t_aut (\<sigma> \<rightarrow>\<^sub>o \<tau>) f)
            (pp_t_aut (\<sigma> \<rightarrow>\<^sub>o \<tau>) g)
          \<longleftrightarrow>
         pp_t_eqv (\<sigma> \<rightarrow>\<^sub>o \<tau>)
            (pp_t_root_swap w) f g)"
  proof -
    fix w f g
    assume f: "Elem f (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
      and g: "Elem g (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    have af:
        "Elem (pp_t_aut (\<sigma> \<rightarrow>\<^sub>o \<tau>) f)
          (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
      using domain[OF f] .
    have ag:
        "Elem (pp_t_aut (\<sigma> \<rightarrow>\<^sub>o \<tau>) g)
          (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
      using domain[OF g] .
    have forward:
        "pp_t_eqv (\<sigma> \<rightarrow>\<^sub>o \<tau>) w
          (pp_t_aut (\<sigma> \<rightarrow>\<^sub>o \<tau>) f)
          (pp_t_aut (\<sigma> \<rightarrow>\<^sub>o \<tau>) g)
        \<Longrightarrow>
        pp_t_eqv (\<sigma> \<rightarrow>\<^sub>o \<tau>)
          (pp_t_root_swap w) f g"
    proof -
      assume left:
          "pp_t_eqv (\<sigma> \<rightarrow>\<^sub>o \<tau>) w
            (pp_t_aut (\<sigma> \<rightarrow>\<^sub>o \<tau>) f)
            (pp_t_aut (\<sigma> \<rightarrow>\<^sub>o \<tau>) g)"
      show "pp_t_eqv (\<sigma> \<rightarrow>\<^sub>o \<tau>)
          (pp_t_root_swap w) f g"
        unfolding pp_t_eqv.simps
      proof (intro allI impI)
        fix v a b
        assume future: "prefix (pp_t_root_swap w) v"
          and a: "Elem a (pp_t_domain \<sigma>)"
          and b: "Elem b (pp_t_domain \<sigma>)"
          and ab: "pp_t_eqv \<sigma> v a b"
        let ?u = "pp_t_root_swap v"
        let ?x = "pp_t_aut \<sigma> a"
        let ?y = "pp_t_aut \<sigma> b"
        have u_future: "prefix w ?u"
          using future
          by (metis pp_t_root_swap_involution
              pp_t_root_swap_prefix_iff)
        have x: "Elem ?x (pp_t_domain \<sigma>)"
          using sigma_domain[OF a] .
        have y: "Elem ?y (pp_t_domain \<sigma>)"
          using sigma_domain[OF b] .
        have xy: "pp_t_eqv \<sigma> ?u ?x ?y"
          using sigma_equivariance[OF a b, of ?u] ab by simp
        have left_apps:
            "pp_t_eqv \<tau> ?u
              (pp_t_aut (\<sigma> \<rightarrow>\<^sub>o \<tau>) f \<acute> ?x)
              (pp_t_aut (\<sigma> \<rightarrow>\<^sub>o \<tau>) g \<acute> ?y)"
          using left u_future x y xy by simp
        have fa: "Elem (f \<acute> a) (pp_t_domain \<tau>)"
          using pp_t_app_closed[OF f a] .
        have gb: "Elem (g \<acute> b) (pp_t_domain \<tau>)"
          using pp_t_app_closed[OF g b] .
        have f_rewrite:
            "pp_t_aut (\<sigma> \<rightarrow>\<^sub>o \<tau>) f \<acute> ?x
              = pp_t_aut \<tau> (f \<acute> a)"
          using pp_t_aut_apply[OF x]
            sigma_involution[OF a]
          by simp
        have g_rewrite:
            "pp_t_aut (\<sigma> \<rightarrow>\<^sub>o \<tau>) g \<acute> ?y
              = pp_t_aut \<tau> (g \<acute> b)"
          using pp_t_aut_apply[OF y]
            sigma_involution[OF b]
          by simp
        have rewritten:
            "pp_t_eqv \<tau> ?u
              (pp_t_aut \<tau> (f \<acute> a))
              (pp_t_aut \<tau> (g \<acute> b))"
          using left_apps f_rewrite g_rewrite by simp
        show "pp_t_eqv \<tau> v (f \<acute> a) (g \<acute> b)"
          using tau_equivariance[OF fa gb, of ?u] rewritten
          by simp
      qed
    qed
    have backward:
        "pp_t_eqv (\<sigma> \<rightarrow>\<^sub>o \<tau>)
            (pp_t_root_swap w) f g
          \<Longrightarrow>
          pp_t_eqv (\<sigma> \<rightarrow>\<^sub>o \<tau>) w
            (pp_t_aut (\<sigma> \<rightarrow>\<^sub>o \<tau>) f)
            (pp_t_aut (\<sigma> \<rightarrow>\<^sub>o \<tau>) g)"
    proof -
      assume right:
          "pp_t_eqv (\<sigma> \<rightarrow>\<^sub>o \<tau>)
            (pp_t_root_swap w) f g"
      show "pp_t_eqv (\<sigma> \<rightarrow>\<^sub>o \<tau>) w
          (pp_t_aut (\<sigma> \<rightarrow>\<^sub>o \<tau>) f)
          (pp_t_aut (\<sigma> \<rightarrow>\<^sub>o \<tau>) g)"
        unfolding pp_t_eqv.simps
      proof (intro allI impI)
        fix v x y
        assume future: "prefix w v"
          and x: "Elem x (pp_t_domain \<sigma>)"
          and y: "Elem y (pp_t_domain \<sigma>)"
          and xy: "pp_t_eqv \<sigma> v x y"
        let ?u = "pp_t_root_swap v"
        have u_future:
            "prefix (pp_t_root_swap w) ?u"
          using future by simp
        have ax: "Elem (pp_t_aut \<sigma> x) (pp_t_domain \<sigma>)"
          using sigma_domain[OF x] .
        have ay: "Elem (pp_t_aut \<sigma> y) (pp_t_domain \<sigma>)"
          using sigma_domain[OF y] .
        have axy:
            "pp_t_eqv \<sigma> ?u
              (pp_t_aut \<sigma> x) (pp_t_aut \<sigma> y)"
          using sigma_equivariance[OF x y, of ?u] xy by simp
        have right_apps:
            "pp_t_eqv \<tau> ?u
              (f \<acute> pp_t_aut \<sigma> x)
              (g \<acute> pp_t_aut \<sigma> y)"
          using right u_future ax ay axy by simp
        have fax:
            "Elem (f \<acute> pp_t_aut \<sigma> x) (pp_t_domain \<tau>)"
          using pp_t_app_closed[OF f ax] .
        have gay:
            "Elem (g \<acute> pp_t_aut \<sigma> y) (pp_t_domain \<tau>)"
          using pp_t_app_closed[OF g ay] .
        have desired:
            "pp_t_eqv \<tau> v
              (pp_t_aut \<tau> (f \<acute> pp_t_aut \<sigma> x))
              (pp_t_aut \<tau> (g \<acute> pp_t_aut \<sigma> y))"
          using tau_equivariance[OF fax gay, of v]
            right_apps by simp
        have f_rewrite:
            "pp_t_aut (\<sigma> \<rightarrow>\<^sub>o \<tau>) f \<acute> x
              = pp_t_aut \<tau> (f \<acute> pp_t_aut \<sigma> x)"
          using pp_t_aut_apply[OF x] .
        have g_rewrite:
            "pp_t_aut (\<sigma> \<rightarrow>\<^sub>o \<tau>) g \<acute> y
              = pp_t_aut \<tau> (g \<acute> pp_t_aut \<sigma> y)"
          using pp_t_aut_apply[OF y] .
        show "pp_t_eqv \<tau> v
            (pp_t_aut (\<sigma> \<rightarrow>\<^sub>o \<tau>) f \<acute> x)
            (pp_t_aut (\<sigma> \<rightarrow>\<^sub>o \<tau>) g \<acute> y)"
          using desired f_rewrite g_rewrite by simp
      qed
    qed
    show "pp_t_eqv (\<sigma> \<rightarrow>\<^sub>o \<tau>) w
          (pp_t_aut (\<sigma> \<rightarrow>\<^sub>o \<tau>) f)
          (pp_t_aut (\<sigma> \<rightarrow>\<^sub>o \<tau>) g)
        \<longleftrightarrow>
        pp_t_eqv (\<sigma> \<rightarrow>\<^sub>o \<tau>)
          (pp_t_root_swap w) f g"
      using forward backward by blast
  qed

  show ?case
    using domain involution equivariance by blast
qed

lemma pp_t_aut_in_domain:
  assumes "Elem x (pp_t_domain \<sigma>)"
  shows "Elem (pp_t_aut \<sigma> x) (pp_t_domain \<sigma>)"
  using pp_t_aut_type_package assms by blast

lemma pp_t_aut_involution:
  assumes "Elem x (pp_t_domain \<sigma>)"
  shows "pp_t_aut \<sigma> (pp_t_aut \<sigma> x) = x"
  using pp_t_aut_type_package assms by blast

lemma pp_t_aut_eqv_iff:
  assumes x: "Elem x (pp_t_domain \<sigma>)"
    and y: "Elem y (pp_t_domain \<sigma>)"
  shows "pp_t_eqv \<sigma> w
      (pp_t_aut \<sigma> x) (pp_t_aut \<sigma> y)
    \<longleftrightarrow>
    pp_t_eqv \<sigma> (pp_t_root_swap w) x y"
  using pp_t_aut_type_package x y by blast

definition pp_t_aut_env ::
    "ctx \<Rightarrow> (nat \<Rightarrow> ZF) \<Rightarrow> nat \<Rightarrow> ZF"
where
  "pp_t_aut_env \<Gamma> \<rho> n =
    (case lookup \<Gamma> n of
       Some \<sigma> \<Rightarrow> pp_t_aut \<sigma> (\<rho> n)
     | None \<Rightarrow> \<rho> n)"

lemma pp_t_aut_env_lookup:
  assumes "lookup \<Gamma> n = Some \<sigma>"
  shows "pp_t_aut_env \<Gamma> \<rho> n = pp_t_aut \<sigma> (\<rho> n)"
  using assms by (simp add: pp_t_aut_env_def)

lemma pp_t_aut_env_typed:
  assumes env: "pp_t_env_typed \<Gamma> \<rho>"
  shows "pp_t_env_typed \<Gamma> (pp_t_aut_env \<Gamma> \<rho>)"
  unfolding pp_t_env_typed_def
  using env pp_t_aut_in_domain
  by (metis pp_t_aut_env_lookup pp_t_env_typed_lookup)

lemma pp_t_aut_env_extend:
  "pp_t_aut_env (\<sigma> # \<Gamma>) (extend_env x \<rho>) =
    extend_env (pp_t_aut \<sigma> x) (pp_t_aut_env \<Gamma> \<rho>)"
proof (rule ext)
  fix n
  show "pp_t_aut_env (\<sigma> # \<Gamma>) (extend_env x \<rho>) n =
      extend_env (pp_t_aut \<sigma> x) (pp_t_aut_env \<Gamma> \<rho>) n"
  proof (cases n)
    case 0
    then show ?thesis
      by (simp add: pp_t_aut_env_def extend_env.simps)
  next
    case (Suc m)
    show ?thesis
    proof (cases "lookup \<Gamma> m")
      case None
      then show ?thesis
        using Suc
        by (simp add: pp_t_aut_env_def extend_env.simps)
    next
      case (Some \<tau>)
      then show ?thesis
        using Suc
        by (simp add: pp_t_aut_env_def extend_env.simps)
    qed
  qed
qed

lemma pp_t_aut_empty_env[simp]:
  "pp_t_aut_env [] \<rho> = \<rho>"
  by (rule ext) (simp add: pp_t_aut_env_def lookup_def)

theorem pp_t_aut_eval:
  assumes typed: "\<Gamma> \<turnstile> M : \<sigma>"
    and logical: "pp_logical_vocabulary M"
    and env: "pp_t_env_typed \<Gamma> \<rho>"
  shows "pp_t_aut \<sigma>
      (pp_t_eval pp_t_default_constants \<rho> M)
    =
    pp_t_eval pp_t_default_constants
      (pp_t_aut_env \<Gamma> \<rho>) M"
  using typed logical env
proof (induction arbitrary: \<rho> rule: has_type.induct)
  case (Var \<Gamma> n \<sigma>)
  then show ?case
    by (simp add: pp_t_aut_env_lookup)
next
  case (Const \<Gamma> c \<sigma>)
  then show ?case
    by (simp add: pp_logical_vocabulary_def)
next
  case (App \<Gamma> M \<sigma> \<tau> N)
  have M_logical: "pp_logical_vocabulary M"
    using App.prems(1)
    by (simp add: pp_logical_vocabulary_def)
  have N_logical: "pp_logical_vocabulary N"
    using App.prems(1)
    by (simp add: pp_logical_vocabulary_def)
  have M_domain:
      "Elem (pp_t_eval pp_t_default_constants \<rho> M)
        (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    using DefaultTreeConstants.pp_t_eval_type[
      OF App.hyps(1) App.prems(2)]
    by (simp add: pp_t_dom_def)
  have N_domain:
      "Elem (pp_t_eval pp_t_default_constants \<rho> N)
        (pp_t_domain \<sigma>)"
    using DefaultTreeConstants.pp_t_eval_type[
      OF App.hyps(2) App.prems(2)]
    by (simp add: pp_t_dom_def)
  have aut_N_domain:
      "Elem
        (pp_t_aut \<sigma>
          (pp_t_eval pp_t_default_constants \<rho> N))
        (pp_t_domain \<sigma>)"
    using pp_t_aut_in_domain[OF N_domain] .
  have aut_aut_N:
      "pp_t_aut \<sigma>
        (pp_t_aut \<sigma>
          (pp_t_eval pp_t_default_constants \<rho> N))
      =
      pp_t_eval pp_t_default_constants \<rho> N"
    using pp_t_aut_involution[OF N_domain] .
  have action:
      "pp_t_aut (\<sigma> \<rightarrow>\<^sub>o \<tau>)
          (pp_t_eval pp_t_default_constants \<rho> M)
          \<acute>
          pp_t_aut \<sigma>
            (pp_t_eval pp_t_default_constants \<rho> N)
        =
       pp_t_aut \<tau>
         (pp_t_eval pp_t_default_constants \<rho> M
           \<acute>
           pp_t_aut \<sigma>
             (pp_t_aut \<sigma>
               (pp_t_eval pp_t_default_constants \<rho> N)))"
    using pp_t_aut_apply[OF aut_N_domain] .
  have action_reduced:
      "pp_t_aut \<tau>
          (pp_t_eval pp_t_default_constants \<rho> M
            \<acute> pp_t_eval pp_t_default_constants \<rho> N)
        =
       pp_t_aut (\<sigma> \<rightarrow>\<^sub>o \<tau>)
          (pp_t_eval pp_t_default_constants \<rho> M)
          \<acute>
          pp_t_aut \<sigma>
            (pp_t_eval pp_t_default_constants \<rho> N)"
    using action aut_aut_N by simp
  show ?case
    unfolding pp_t_eval.simps
    using action_reduced
      App.IH(1)[OF M_logical App.prems(2)]
      App.IH(2)[OF N_logical App.prems(2)]
    by simp
next
  case (Lam \<sigma> \<Gamma> M \<tau>)
  have M_logical: "pp_logical_vocabulary M"
    using Lam.prems(1)
    by (simp add: pp_logical_vocabulary_def)
  have pointwise:
      "\<forall>x. Elem x (pp_t_domain \<sigma>) \<longrightarrow>
        pp_t_aut \<tau>
          (pp_t_eval pp_t_default_constants
            (extend_env (pp_t_aut \<sigma> x) \<rho>) M)
        =
        pp_t_eval pp_t_default_constants
          (extend_env x (pp_t_aut_env \<Gamma> \<rho>)) M"
  proof (intro allI impI)
    fix x
    assume x: "Elem x (pp_t_domain \<sigma>)"
    have ax: "Elem (pp_t_aut \<sigma> x) (pp_t_domain \<sigma>)"
      using pp_t_aut_in_domain[OF x] .
    have body_equivariance:
        "pp_t_aut \<tau>
          (pp_t_eval pp_t_default_constants
            (extend_env (pp_t_aut \<sigma> x) \<rho>) M)
        =
        pp_t_eval pp_t_default_constants
          (pp_t_aut_env (\<sigma> # \<Gamma>)
            (extend_env (pp_t_aut \<sigma> x) \<rho>)) M"
      using Lam.IH[
        OF M_logical
          pp_t_env_typed_extend[OF Lam.prems(2) ax]] .
    have env_rewrite:
        "pp_t_aut_env (\<sigma> # \<Gamma>)
            (extend_env (pp_t_aut \<sigma> x) \<rho>)
          =
         extend_env x (pp_t_aut_env \<Gamma> \<rho>)"
      using pp_t_aut_env_extend[of \<sigma> \<Gamma>
          "pp_t_aut \<sigma> x" \<rho>]
        pp_t_aut_involution[OF x]
      by simp
    show "pp_t_aut \<tau>
          (pp_t_eval pp_t_default_constants
            (extend_env (pp_t_aut \<sigma> x) \<rho>) M)
        =
        pp_t_eval pp_t_default_constants
          (extend_env x (pp_t_aut_env \<Gamma> \<rho>)) M"
      using body_equivariance env_rewrite by simp
  qed
  have pointwise_after_application:
      "\<forall>x. Elem x (pp_t_domain \<sigma>) \<longrightarrow>
        pp_t_aut \<tau>
          (Lambda (pp_t_domain \<sigma>)
            (\<lambda>y. pp_t_eval pp_t_default_constants
              (extend_env y \<rho>) M)
            \<acute> pp_t_aut \<sigma> x)
        =
        pp_t_eval pp_t_default_constants
          (extend_env x (pp_t_aut_env \<Gamma> \<rho>)) M"
  proof (intro allI impI)
    fix x
    assume x: "Elem x (pp_t_domain \<sigma>)"
    have ax: "Elem (pp_t_aut \<sigma> x) (pp_t_domain \<sigma>)"
      using pp_t_aut_in_domain[OF x] .
    have at_x:
        "pp_t_aut \<tau>
          (pp_t_eval pp_t_default_constants
            (extend_env (pp_t_aut \<sigma> x) \<rho>) M)
        =
        pp_t_eval pp_t_default_constants
          (extend_env x (pp_t_aut_env \<Gamma> \<rho>)) M"
      using pointwise x by blast
    show "pp_t_aut \<tau>
          (Lambda (pp_t_domain \<sigma>)
            (\<lambda>y. pp_t_eval pp_t_default_constants
              (extend_env y \<rho>) M)
            \<acute> pp_t_aut \<sigma> x)
        =
        pp_t_eval pp_t_default_constants
          (extend_env x (pp_t_aut_env \<Gamma> \<rho>)) M"
      using at_x ax by (simp add: Lambda_app)
  qed
  show ?case
    unfolding pp_t_eval.simps pp_t_aut.simps
    using pointwise_after_application by (simp add: Lambda_ext)
next
  case (Eq \<Gamma> M \<sigma> N)
  have M_logical: "pp_logical_vocabulary M"
    using Eq.prems(1)
    by (simp add: pp_logical_vocabulary_def)
  have N_logical: "pp_logical_vocabulary N"
    using Eq.prems(1)
    by (simp add: pp_logical_vocabulary_def)
  have M_domain:
      "Elem (pp_t_eval pp_t_default_constants \<rho> M)
        (pp_t_domain \<sigma>)"
    using DefaultTreeConstants.pp_t_eval_type[
      OF Eq.hyps(1) Eq.prems(2)]
    by (simp add: pp_t_dom_def)
  have N_domain:
      "Elem (pp_t_eval pp_t_default_constants \<rho> N)
        (pp_t_domain \<sigma>)"
    using DefaultTreeConstants.pp_t_eval_type[
      OF Eq.hyps(2) Eq.prems(2)]
    by (simp add: pp_t_dom_def)
  show ?case
  proof (rule pp_t_prop_ext)
    show "Elem
        (pp_t_aut Prop
          (pp_t_eval pp_t_default_constants \<rho> (Eq \<sigma> M N)))
        (pp_t_domain Prop)"
      unfolding pp_t_aut.simps
      by (rule pp_t_prop_in_domain)
    show "Elem
        (pp_t_eval pp_t_default_constants
          (pp_t_aut_env \<Gamma> \<rho>) (Eq \<sigma> M N))
        (pp_t_domain Prop)"
      unfolding pp_t_eval.simps
      by (rule pp_t_prop_in_domain)
    fix w
    show "pp_t_holds
          (pp_t_aut Prop
            (pp_t_eval pp_t_default_constants \<rho> (Eq \<sigma> M N))) w
        =
        pp_t_holds
          (pp_t_eval pp_t_default_constants
            (pp_t_aut_env \<Gamma> \<rho>) (Eq \<sigma> M N)) w"
      using Eq.IH(1)[OF M_logical Eq.prems(2)]
        Eq.IH(2)[OF N_logical Eq.prems(2)]
        pp_t_aut_eqv_iff[OF M_domain N_domain, of w]
      by simp
  qed
next
  case (Neg \<Gamma> A)
  have A_logical: "pp_logical_vocabulary A"
    using Neg.prems(1)
    by (simp add: pp_logical_vocabulary_def)
  show ?case
  proof (rule pp_t_prop_ext)
    show "Elem
        (pp_t_aut Prop
          (pp_t_eval pp_t_default_constants \<rho> (Neg A)))
        (pp_t_domain Prop)"
      unfolding pp_t_aut.simps
      by (rule pp_t_prop_in_domain)
    show "Elem
        (pp_t_eval pp_t_default_constants
          (pp_t_aut_env \<Gamma> \<rho>) (Neg A))
        (pp_t_domain Prop)"
      unfolding pp_t_eval.simps
      by (rule pp_t_prop_in_domain)
    fix w
    have A_at:
        "pp_t_holds
          (pp_t_aut Prop
            (pp_t_eval pp_t_default_constants \<rho> A)) w
        =
        pp_t_holds
          (pp_t_eval pp_t_default_constants
            (pp_t_aut_env \<Gamma> \<rho>) A) w"
      using arg_cong[OF Neg.IH[OF A_logical Neg.prems(2)],
          of "\<lambda>P. pp_t_holds P w"] .
    show "pp_t_holds
          (pp_t_aut Prop
            (pp_t_eval pp_t_default_constants \<rho> (Neg A))) w
        =
        pp_t_holds
          (pp_t_eval pp_t_default_constants
            (pp_t_aut_env \<Gamma> \<rho>) (Neg A)) w"
      using A_at by simp
  qed
next
  case (Conj \<Gamma> A B)
  have A_logical: "pp_logical_vocabulary A"
    using Conj.prems(1)
    by (simp add: pp_logical_vocabulary_def)
  have B_logical: "pp_logical_vocabulary B"
    using Conj.prems(1)
    by (simp add: pp_logical_vocabulary_def)
  show ?case
  proof (rule pp_t_prop_ext)
    show "Elem
        (pp_t_aut Prop
          (pp_t_eval pp_t_default_constants \<rho> (Conj A B)))
        (pp_t_domain Prop)"
      unfolding pp_t_aut.simps
      by (rule pp_t_prop_in_domain)
    show "Elem
        (pp_t_eval pp_t_default_constants
          (pp_t_aut_env \<Gamma> \<rho>) (Conj A B))
        (pp_t_domain Prop)"
      unfolding pp_t_eval.simps
      by (rule pp_t_prop_in_domain)
    fix w
    have A_at:
        "pp_t_holds
          (pp_t_aut Prop
            (pp_t_eval pp_t_default_constants \<rho> A)) w
        =
        pp_t_holds
          (pp_t_eval pp_t_default_constants
            (pp_t_aut_env \<Gamma> \<rho>) A) w"
      using arg_cong[OF Conj.IH(1)[OF A_logical Conj.prems(2)],
          of "\<lambda>P. pp_t_holds P w"] .
    have B_at:
        "pp_t_holds
          (pp_t_aut Prop
            (pp_t_eval pp_t_default_constants \<rho> B)) w
        =
        pp_t_holds
          (pp_t_eval pp_t_default_constants
            (pp_t_aut_env \<Gamma> \<rho>) B) w"
      using arg_cong[OF Conj.IH(2)[OF B_logical Conj.prems(2)],
          of "\<lambda>P. pp_t_holds P w"] .
    show "pp_t_holds
          (pp_t_aut Prop
            (pp_t_eval pp_t_default_constants \<rho> (Conj A B))) w
        =
        pp_t_holds
          (pp_t_eval pp_t_default_constants
            (pp_t_aut_env \<Gamma> \<rho>) (Conj A B)) w"
      using A_at B_at by simp
  qed
next
  case (Disj \<Gamma> A B)
  have A_logical: "pp_logical_vocabulary A"
    using Disj.prems(1)
    by (simp add: pp_logical_vocabulary_def)
  have B_logical: "pp_logical_vocabulary B"
    using Disj.prems(1)
    by (simp add: pp_logical_vocabulary_def)
  show ?case
  proof (rule pp_t_prop_ext)
    show "Elem
        (pp_t_aut Prop
          (pp_t_eval pp_t_default_constants \<rho> (Disj A B)))
        (pp_t_domain Prop)"
      unfolding pp_t_aut.simps
      by (rule pp_t_prop_in_domain)
    show "Elem
        (pp_t_eval pp_t_default_constants
          (pp_t_aut_env \<Gamma> \<rho>) (Disj A B))
        (pp_t_domain Prop)"
      unfolding pp_t_eval.simps
      by (rule pp_t_prop_in_domain)
    fix w
    have A_at:
        "pp_t_holds
          (pp_t_aut Prop
            (pp_t_eval pp_t_default_constants \<rho> A)) w
        =
        pp_t_holds
          (pp_t_eval pp_t_default_constants
            (pp_t_aut_env \<Gamma> \<rho>) A) w"
      using arg_cong[OF Disj.IH(1)[OF A_logical Disj.prems(2)],
          of "\<lambda>P. pp_t_holds P w"] .
    have B_at:
        "pp_t_holds
          (pp_t_aut Prop
            (pp_t_eval pp_t_default_constants \<rho> B)) w
        =
        pp_t_holds
          (pp_t_eval pp_t_default_constants
            (pp_t_aut_env \<Gamma> \<rho>) B) w"
      using arg_cong[OF Disj.IH(2)[OF B_logical Disj.prems(2)],
          of "\<lambda>P. pp_t_holds P w"] .
    show "pp_t_holds
          (pp_t_aut Prop
            (pp_t_eval pp_t_default_constants \<rho> (Disj A B))) w
        =
        pp_t_holds
          (pp_t_eval pp_t_default_constants
            (pp_t_aut_env \<Gamma> \<rho>) (Disj A B)) w"
      using A_at B_at by simp
  qed
next
  case (Imp \<Gamma> A B)
  have A_logical: "pp_logical_vocabulary A"
    using Imp.prems(1)
    by (simp add: pp_logical_vocabulary_def)
  have B_logical: "pp_logical_vocabulary B"
    using Imp.prems(1)
    by (simp add: pp_logical_vocabulary_def)
  show ?case
  proof (rule pp_t_prop_ext)
    show "Elem
        (pp_t_aut Prop
          (pp_t_eval pp_t_default_constants \<rho> (Imp A B)))
        (pp_t_domain Prop)"
      unfolding pp_t_aut.simps
      by (rule pp_t_prop_in_domain)
    show "Elem
        (pp_t_eval pp_t_default_constants
          (pp_t_aut_env \<Gamma> \<rho>) (Imp A B))
        (pp_t_domain Prop)"
      unfolding pp_t_eval.simps
      by (rule pp_t_prop_in_domain)
    fix w
    have A_at:
        "pp_t_holds
          (pp_t_aut Prop
            (pp_t_eval pp_t_default_constants \<rho> A)) w
        =
        pp_t_holds
          (pp_t_eval pp_t_default_constants
            (pp_t_aut_env \<Gamma> \<rho>) A) w"
      using arg_cong[OF Imp.IH(1)[OF A_logical Imp.prems(2)],
          of "\<lambda>P. pp_t_holds P w"] .
    have B_at:
        "pp_t_holds
          (pp_t_aut Prop
            (pp_t_eval pp_t_default_constants \<rho> B)) w
        =
        pp_t_holds
          (pp_t_eval pp_t_default_constants
            (pp_t_aut_env \<Gamma> \<rho>) B) w"
      using arg_cong[OF Imp.IH(2)[OF B_logical Imp.prems(2)],
          of "\<lambda>P. pp_t_holds P w"] .
    show "pp_t_holds
          (pp_t_aut Prop
            (pp_t_eval pp_t_default_constants \<rho> (Imp A B))) w
        =
        pp_t_holds
          (pp_t_eval pp_t_default_constants
            (pp_t_aut_env \<Gamma> \<rho>) (Imp A B)) w"
      using A_at B_at by simp
  qed
next
  case (Forall \<sigma> \<Gamma> A)
  have A_logical: "pp_logical_vocabulary A"
    using Forall.prems(1)
    by (simp add: pp_logical_vocabulary_def)
  show ?case
  proof (rule pp_t_prop_ext)
    show "Elem
        (pp_t_aut Prop
          (pp_t_eval pp_t_default_constants \<rho> (Forall \<sigma> A)))
        (pp_t_domain Prop)"
      unfolding pp_t_aut.simps
      by (rule pp_t_prop_in_domain)
    show "Elem
        (pp_t_eval pp_t_default_constants
          (pp_t_aut_env \<Gamma> \<rho>) (Forall \<sigma> A))
        (pp_t_domain Prop)"
      unfolding pp_t_eval.simps
      by (rule pp_t_prop_in_domain)
    fix w
    have body:
        "\<And>x. Elem x (pp_t_domain \<sigma>) \<Longrightarrow>
          pp_t_aut Prop
            (pp_t_eval pp_t_default_constants
              (extend_env x \<rho>) A)
          =
          pp_t_eval pp_t_default_constants
            (extend_env (pp_t_aut \<sigma> x)
              (pp_t_aut_env \<Gamma> \<rho>)) A"
    proof -
      fix x
      assume x: "Elem x (pp_t_domain \<sigma>)"
      have raw:
          "pp_t_aut Prop
            (pp_t_eval pp_t_default_constants
              (extend_env x \<rho>) A)
          =
          pp_t_eval pp_t_default_constants
            (pp_t_aut_env (\<sigma> # \<Gamma>)
              (extend_env x \<rho>)) A"
        using Forall.IH[
          OF A_logical
            pp_t_env_typed_extend[OF Forall.prems(2) x]] .
      show "pp_t_aut Prop
            (pp_t_eval pp_t_default_constants
              (extend_env x \<rho>) A)
          =
          pp_t_eval pp_t_default_constants
            (extend_env (pp_t_aut \<sigma> x)
              (pp_t_aut_env \<Gamma> \<rho>)) A"
        using raw by (simp add: pp_t_aut_env_extend)
    qed
    have pointwise:
        "\<And>x. Elem x (pp_t_domain \<sigma>) \<Longrightarrow>
          pp_t_holds
            (pp_t_eval pp_t_default_constants
              (extend_env x \<rho>) A)
            (pp_t_root_swap w)
          =
          pp_t_holds
            (pp_t_eval pp_t_default_constants
              (extend_env (pp_t_aut \<sigma> x)
                (pp_t_aut_env \<Gamma> \<rho>)) A) w"
    proof -
      fix x
      assume x: "Elem x (pp_t_domain \<sigma>)"
      have at_w:
          "pp_t_holds
            (pp_t_aut Prop
              (pp_t_eval pp_t_default_constants
                (extend_env x \<rho>) A)) w
          =
          pp_t_holds
            (pp_t_eval pp_t_default_constants
              (extend_env (pp_t_aut \<sigma> x)
                (pp_t_aut_env \<Gamma> \<rho>)) A) w"
        using arg_cong[OF body[OF x],
            of "\<lambda>P. pp_t_holds P w"] .
      show "pp_t_holds
            (pp_t_eval pp_t_default_constants
              (extend_env x \<rho>) A)
            (pp_t_root_swap w)
          =
          pp_t_holds
            (pp_t_eval pp_t_default_constants
              (extend_env (pp_t_aut \<sigma> x)
                (pp_t_aut_env \<Gamma> \<rho>)) A) w"
        using at_w by simp
    qed
    have quantified:
        "(\<forall>x.
          Elem x (pp_t_domain \<sigma>) \<longrightarrow>
          pp_t_holds
            (pp_t_eval pp_t_default_constants
              (extend_env x \<rho>) A)
            (pp_t_root_swap w))
        =
        (\<forall>x.
          Elem x (pp_t_domain \<sigma>) \<longrightarrow>
          pp_t_holds
            (pp_t_eval pp_t_default_constants
              (extend_env x (pp_t_aut_env \<Gamma> \<rho>)) A) w)"
      using pointwise pp_t_aut_in_domain pp_t_aut_involution
      by metis
    show "pp_t_holds
          (pp_t_aut Prop
            (pp_t_eval pp_t_default_constants \<rho> (Forall \<sigma> A))) w
        =
        pp_t_holds
          (pp_t_eval pp_t_default_constants
            (pp_t_aut_env \<Gamma> \<rho>) (Forall \<sigma> A)) w"
      using quantified by simp
  qed
next
  case (Exists \<sigma> \<Gamma> A)
  have A_logical: "pp_logical_vocabulary A"
    using Exists.prems(1)
    by (simp add: pp_logical_vocabulary_def)
  show ?case
  proof (rule pp_t_prop_ext)
    show "Elem
        (pp_t_aut Prop
          (pp_t_eval pp_t_default_constants \<rho> (Exists \<sigma> A)))
        (pp_t_domain Prop)"
      unfolding pp_t_aut.simps
      by (rule pp_t_prop_in_domain)
    show "Elem
        (pp_t_eval pp_t_default_constants
          (pp_t_aut_env \<Gamma> \<rho>) (Exists \<sigma> A))
        (pp_t_domain Prop)"
      unfolding pp_t_eval.simps
      by (rule pp_t_prop_in_domain)
    fix w
    have body:
        "\<And>x. Elem x (pp_t_domain \<sigma>) \<Longrightarrow>
          pp_t_aut Prop
            (pp_t_eval pp_t_default_constants
              (extend_env x \<rho>) A)
          =
          pp_t_eval pp_t_default_constants
            (extend_env (pp_t_aut \<sigma> x)
              (pp_t_aut_env \<Gamma> \<rho>)) A"
    proof -
      fix x
      assume x: "Elem x (pp_t_domain \<sigma>)"
      have raw:
          "pp_t_aut Prop
            (pp_t_eval pp_t_default_constants
              (extend_env x \<rho>) A)
          =
          pp_t_eval pp_t_default_constants
            (pp_t_aut_env (\<sigma> # \<Gamma>)
              (extend_env x \<rho>)) A"
        using Exists.IH[
          OF A_logical
            pp_t_env_typed_extend[OF Exists.prems(2) x]] .
      show "pp_t_aut Prop
            (pp_t_eval pp_t_default_constants
              (extend_env x \<rho>) A)
          =
          pp_t_eval pp_t_default_constants
            (extend_env (pp_t_aut \<sigma> x)
              (pp_t_aut_env \<Gamma> \<rho>)) A"
        using raw by (simp add: pp_t_aut_env_extend)
    qed
    have pointwise:
        "\<And>x. Elem x (pp_t_domain \<sigma>) \<Longrightarrow>
          pp_t_holds
            (pp_t_eval pp_t_default_constants
              (extend_env x \<rho>) A)
            (pp_t_root_swap w)
          =
          pp_t_holds
            (pp_t_eval pp_t_default_constants
              (extend_env (pp_t_aut \<sigma> x)
                (pp_t_aut_env \<Gamma> \<rho>)) A) w"
    proof -
      fix x
      assume x: "Elem x (pp_t_domain \<sigma>)"
      have at_w:
          "pp_t_holds
            (pp_t_aut Prop
              (pp_t_eval pp_t_default_constants
                (extend_env x \<rho>) A)) w
          =
          pp_t_holds
            (pp_t_eval pp_t_default_constants
              (extend_env (pp_t_aut \<sigma> x)
                (pp_t_aut_env \<Gamma> \<rho>)) A) w"
        using arg_cong[OF body[OF x],
            of "\<lambda>P. pp_t_holds P w"] .
      show "pp_t_holds
            (pp_t_eval pp_t_default_constants
              (extend_env x \<rho>) A)
            (pp_t_root_swap w)
          =
          pp_t_holds
            (pp_t_eval pp_t_default_constants
              (extend_env (pp_t_aut \<sigma> x)
                (pp_t_aut_env \<Gamma> \<rho>)) A) w"
        using at_w by simp
    qed
    have quantified:
        "(\<exists>x.
          Elem x (pp_t_domain \<sigma>) \<and>
          pp_t_holds
            (pp_t_eval pp_t_default_constants
              (extend_env x \<rho>) A)
            (pp_t_root_swap w))
        =
        (\<exists>x.
          Elem x (pp_t_domain \<sigma>) \<and>
          pp_t_holds
            (pp_t_eval pp_t_default_constants
              (extend_env x (pp_t_aut_env \<Gamma> \<rho>)) A) w)"
      using pointwise pp_t_aut_in_domain pp_t_aut_involution
      by metis
    show "pp_t_holds
          (pp_t_aut Prop
            (pp_t_eval pp_t_default_constants \<rho> (Exists \<sigma> A))) w
        =
        pp_t_holds
          (pp_t_eval pp_t_default_constants
            (pp_t_aut_env \<Gamma> \<rho>) (Exists \<sigma> A)) w"
      using quantified by simp
  qed
qed

corollary pp_t_closed_logical_den_aut_fixed:
  assumes typed: "[] \<turnstile> M : \<sigma>"
    and logical: "pp_logical_vocabulary M"
  shows "pp_t_aut \<sigma> (pp_t_closed_den M) =
    pp_t_closed_den M"
  unfolding pp_t_closed_den_def
  using pp_t_aut_eval[
    OF typed logical pp_t_empty_env_typed,
    of pp_t_closed_env]
  by simp

end
