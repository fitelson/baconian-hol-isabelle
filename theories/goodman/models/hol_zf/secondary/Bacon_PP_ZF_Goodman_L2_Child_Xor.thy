theory Bacon_PP_ZF_Goodman_L2_Child_Xor
  imports Bacon_PP_ZF_Goodman_L2_Higher_Order_Quantifiers
begin

section \<open>A quantified immediate-successor operator\<close>

text \<open>
  At a world, the atoms of the Boolean algebra of propositions modulo
  world-relative equality are exactly the singleton propositions in the
  current cone.  This lets the object language characterize the two immediate
  successors without naming either branch.
\<close>

definition pp_t_HO_atom_term :: oterm where
  "pp_t_HO_atom_term =
    Lam Prop
      (Conj
        (Neg (Eq Prop (Var 0) ObjFalse))
        (Forall Prop
          (Imp
            (Eq Prop (Var 0) (Conj (Var 0) (Var 1)))
            (Disj
              (Eq Prop (Var 0) ObjFalse)
              (Eq Prop (Var 0) (Var 1))))))"

definition pp_t_HO_immediate_term :: oterm where
  "pp_t_HO_immediate_term =
    Lam Prop
      (Lam Prop
        (Conj
          (App pp_t_HO_atom_term (Var 0))
          (Conj
            (Neg (Var 0))
            (Eq Prop
              (\<diamond>\<^sub>o (Var 0))
              (Disj (Var 1) (Var 0))))))"

definition pp_t_HO_child_xor_term :: oterm where
  "pp_t_HO_child_xor_term =
    Lam Prop
      (Exists Prop
        (Conj
          (App pp_t_HO_atom_term (Var 0))
          (Conj
            (Var 0)
            (Conj
              (Exists Prop
                (Conj
                  (App
                    (App pp_t_HO_immediate_term (Var 1))
                    (Var 0))
                  (Eq Prop
                    (Var 0)
                    (Conj (Var 0) (Var 2)))))
              (Exists Prop
                (Conj
                  (App
                    (App pp_t_HO_immediate_term (Var 1))
                    (Var 0))
                  (Eq Prop
                    (Var 0)
                    (Conj (Var 0) (Neg (Var 2))))))))))"

lemma pp_t_HO_child_xor_terms_typed:
  "[] \<turnstile> pp_t_HO_atom_term : (Prop \<rightarrow>\<^sub>o Prop)"
  "[] \<turnstile> pp_t_HO_immediate_term :
    (Prop \<rightarrow>\<^sub>o Prop \<rightarrow>\<^sub>o Prop)"
  "[] \<turnstile> pp_t_HO_child_xor_term :
    (Prop \<rightarrow>\<^sub>o Prop)"
  by (rule infer_type_sound;
      simp add: pp_t_HO_atom_term_def
        pp_t_HO_immediate_term_def
        pp_t_HO_child_xor_term_def
        ObjFalse_def ObjDiamond_def ObjBox_def ObjTrue_def lookup_def)+

lemma pp_t_HO_child_xor_terms_logical:
  "pp_logical_vocabulary pp_t_HO_atom_term"
  "pp_logical_vocabulary pp_t_HO_immediate_term"
  "pp_logical_vocabulary pp_t_HO_child_xor_term"
  by (simp_all add: pp_logical_vocabulary_def
      pp_t_HO_atom_term_def pp_t_HO_immediate_term_def
      pp_t_HO_child_xor_term_def ObjFalse_def
      ObjDiamond_def ObjBox_def ObjTrue_def)

definition pp_b_child_xor :: pp_b_operator where
  "pp_b_child_xor P =
    {w. (w @ [False] \<in> P) \<noteq> (w @ [True] \<in> P)}"

definition pp_t_atom_at :: "bool list \<Rightarrow> ZF \<Rightarrow> bool" where
  "pp_t_atom_at w Q \<longleftrightarrow>
    (\<exists>v. prefix w v \<and>
      (\<forall>u. prefix w u \<longrightarrow>
        (pp_t_holds Q u \<longleftrightarrow> u = v)))"

lemma pp_t_HO_atom_raw:
  assumes Q: "Elem Q (pp_t_domain Prop)"
  shows "pp_t_holds
      ((pp_t_closed_den pp_t_HO_atom_term) \<acute> Q) w
    \<longleftrightarrow>
    ((\<exists>v. prefix w v \<and> pp_t_holds Q v) \<and>
      (\<forall>R.
        Elem R (pp_t_domain Prop) \<longrightarrow>
        ((\<forall>v. prefix w v \<longrightarrow>
            (pp_t_holds R v \<longrightarrow> pp_t_holds Q v))
          \<longrightarrow>
          ((\<forall>v. prefix w v \<longrightarrow>
              \<not> pp_t_holds R v) \<or>
           (\<forall>v. prefix w v \<longrightarrow>
              (pp_t_holds R v \<longleftrightarrow>
               pp_t_holds Q v))))))"
  using Q
  by (simp add: pp_t_closed_den_def pp_t_HO_atom_term_def
      pp_t_eval_ObjFalse Lambda_app; blast)

theorem pp_t_HO_atom_holds:
  assumes Q: "Elem Q (pp_t_domain Prop)"
  shows "pp_t_holds
      ((pp_t_closed_den pp_t_HO_atom_term) \<acute> Q) w
    \<longleftrightarrow> pp_t_atom_at w Q"
proof
  assume atom:
      "pp_t_holds
        ((pp_t_closed_den pp_t_HO_atom_term) \<acute> Q) w"
  have raw:
      "(\<exists>v. prefix w v \<and> pp_t_holds Q v) \<and>
       (\<forall>R.
        Elem R (pp_t_domain Prop) \<longrightarrow>
        ((\<forall>v. prefix w v \<longrightarrow>
            (pp_t_holds R v \<longrightarrow> pp_t_holds Q v))
          \<longrightarrow>
          ((\<forall>v. prefix w v \<longrightarrow>
              \<not> pp_t_holds R v) \<or>
           (\<forall>v. prefix w v \<longrightarrow>
              (pp_t_holds R v \<longleftrightarrow>
               pp_t_holds Q v)))))"
    using atom pp_t_HO_atom_raw[OF Q, of w] by blast
  then obtain v where v_future: "prefix w v"
    and Q_v: "pp_t_holds Q v"
    by blast
  show "pp_t_atom_at w Q"
    unfolding pp_t_atom_at_def
  proof (intro exI[of _ v] conjI allI impI)
    show "prefix w v"
      by (rule v_future)
  next
    fix u
    assume u_future: "prefix w u"
    show "pp_t_holds Q u \<longleftrightarrow> u = v"
    proof
      assume Q_u: "pp_t_holds Q u"
      let ?R = "pp_zf_of_b {u}"
      have R_domain: "Elem ?R (pp_t_domain Prop)"
        by (rule pp_zf_of_b_in_domain)
      have R_subset:
          "\<forall>t. prefix w t \<longrightarrow>
            (pp_t_holds ?R t \<longrightarrow> pp_t_holds Q t)"
        using Q_u by auto
      have alternatives:
          "(\<forall>t. prefix w t \<longrightarrow>
              \<not> pp_t_holds ?R t) \<or>
           (\<forall>t. prefix w t \<longrightarrow>
              (pp_t_holds ?R t \<longleftrightarrow>
               pp_t_holds Q t))"
        using raw R_domain R_subset by blast
      have not_empty:
          "\<not> (\<forall>t. prefix w t \<longrightarrow>
            \<not> pp_t_holds ?R t)"
        using u_future by auto
      have same:
          "\<forall>t. prefix w t \<longrightarrow>
            (pp_t_holds ?R t \<longleftrightarrow>
             pp_t_holds Q t)"
        using alternatives not_empty by blast
      have "pp_t_holds ?R v"
        using same v_future Q_v by blast
      then show "u = v"
        by simp
    next
      assume "u = v"
      then show "pp_t_holds Q u"
        using Q_v by simp
    qed
  qed
next
  assume atom_at: "pp_t_atom_at w Q"
  then obtain v where v_future: "prefix w v"
    and unique:
      "\<forall>u. prefix w u \<longrightarrow>
        (pp_t_holds Q u \<longleftrightarrow> u = v)"
    unfolding pp_t_atom_at_def by blast
  have Q_v: "pp_t_holds Q v"
    using unique v_future by blast
  have raw:
      "(\<exists>u. prefix w u \<and> pp_t_holds Q u) \<and>
       (\<forall>R.
        Elem R (pp_t_domain Prop) \<longrightarrow>
        ((\<forall>u. prefix w u \<longrightarrow>
            (pp_t_holds R u \<longrightarrow> pp_t_holds Q u))
          \<longrightarrow>
          ((\<forall>u. prefix w u \<longrightarrow>
              \<not> pp_t_holds R u) \<or>
           (\<forall>u. prefix w u \<longrightarrow>
              (pp_t_holds R u \<longleftrightarrow>
               pp_t_holds Q u)))))"
  proof (intro conjI)
    show "\<exists>u. prefix w u \<and> pp_t_holds Q u"
      using v_future Q_v by blast
  next
    show "\<forall>R.
        Elem R (pp_t_domain Prop) \<longrightarrow>
        ((\<forall>u. prefix w u \<longrightarrow>
            (pp_t_holds R u \<longrightarrow> pp_t_holds Q u))
          \<longrightarrow>
          ((\<forall>u. prefix w u \<longrightarrow>
              \<not> pp_t_holds R u) \<or>
           (\<forall>u. prefix w u \<longrightarrow>
              (pp_t_holds R u \<longleftrightarrow>
               pp_t_holds Q u))))"
    proof (intro allI impI)
      fix R
      assume subset:
          "\<forall>u. prefix w u \<longrightarrow>
            (pp_t_holds R u \<longrightarrow> pp_t_holds Q u)"
      show "(\<forall>u. prefix w u \<longrightarrow>
              \<not> pp_t_holds R u) \<or>
          (\<forall>u. prefix w u \<longrightarrow>
              (pp_t_holds R u \<longleftrightarrow>
               pp_t_holds Q u))"
      proof (cases "\<exists>u. prefix w u \<and> pp_t_holds R u")
        case False
        then show ?thesis by blast
      next
        case True
        then obtain u where u_future: "prefix w u"
          and R_u: "pp_t_holds R u"
          by blast
        have Q_u: "pp_t_holds Q u"
          using subset u_future R_u by blast
        have u_v: "u = v"
          using unique u_future Q_u by blast
        have same:
            "\<forall>t. prefix w t \<longrightarrow>
              (pp_t_holds R t \<longleftrightarrow>
               pp_t_holds Q t)"
        proof (intro allI impI iffI)
          fix t
          assume t_future: "prefix w t"
            and R_t: "pp_t_holds R t"
          show "pp_t_holds Q t"
            using subset t_future R_t by blast
        next
          fix t
          assume t_future: "prefix w t"
            and Q_t: "pp_t_holds Q t"
          have "t = v"
            using unique t_future Q_t by blast
          then show "pp_t_holds R t"
            using R_u u_v by simp
        qed
        then show ?thesis by blast
      qed
    qed
  qed
  show "pp_t_holds
      ((pp_t_closed_den pp_t_HO_atom_term) \<acute> Q) w"
    using pp_t_HO_atom_raw[OF Q, of w] raw by blast
qed

lemma pp_t_shift_HO_atom_term[simp]:
  "shift pp_t_HO_atom_term = pp_t_HO_atom_term"
  by (simp add: shift_def pp_t_HO_atom_term_def
      ObjFalse_def ObjTrue_def)

lemma pp_t_rename_HO_atom_term[simp]:
  "rename f pp_t_HO_atom_term = pp_t_HO_atom_term"
  by (simp add: pp_t_HO_atom_term_def
      ObjFalse_def ObjTrue_def)

lemma pp_t_eval_HO_atom_term_extend[simp]:
  "pp_t_eval C (extend_env x \<rho>) pp_t_HO_atom_term =
    pp_t_eval C \<rho> pp_t_HO_atom_term"
  using pp_t_eval_shift[of C x \<rho> pp_t_HO_atom_term]
  by simp

lemma pp_t_shift_HO_immediate_term[simp]:
  "shift pp_t_HO_immediate_term = pp_t_HO_immediate_term"
  by (simp add: shift_def pp_t_HO_immediate_term_def
      ObjDiamond_def ObjBox_def ObjFalse_def ObjTrue_def)

lemma pp_t_eval_HO_immediate_term_extend[simp]:
  "pp_t_eval C (extend_env x \<rho>) pp_t_HO_immediate_term =
    pp_t_eval C \<rho> pp_t_HO_immediate_term"
  using pp_t_eval_shift[of C x \<rho> pp_t_HO_immediate_term]
  by simp

lemma pp_t_HO_immediate_holds:
  assumes C: "Elem C (pp_t_domain Prop)"
    and Q: "Elem Q (pp_t_domain Prop)"
  shows "pp_t_holds
      (((pp_t_closed_den pp_t_HO_immediate_term) \<acute> C)
        \<acute> Q) w
    \<longleftrightarrow>
      pp_t_atom_at w Q \<and>
      \<not> pp_t_holds Q w \<and>
      (\<forall>v. prefix w v \<longrightarrow>
        ((\<exists>u. prefix v u \<and> pp_t_holds Q u)
          \<longleftrightarrow>
         pp_t_holds C v \<or> pp_t_holds Q v))"
  using C Q pp_t_HO_atom_holds[OF Q, of w]
  by (simp add: pp_t_closed_den_def
      pp_t_HO_immediate_term_def ObjDiamond_def ObjBox_def
      ObjFalse_def ObjTrue_def Lambda_app
      pp_t_closed_den_def)

definition pp_t_child_atom_at :: "bool list \<Rightarrow> ZF \<Rightarrow> bool" where
  "pp_t_child_atom_at w Q \<longleftrightarrow>
    (\<exists>b. \<forall>u. prefix w u \<longrightarrow>
      (pp_t_holds Q u \<longleftrightarrow> u = w @ [b]))"

lemma pp_t_atom_at_true_iff:
  assumes atom: "pp_t_atom_at w C"
    and true: "pp_t_holds C w"
  shows "\<forall>u. prefix w u \<longrightarrow>
    (pp_t_holds C u \<longleftrightarrow> u = w)"
proof -
  obtain v where v: "prefix w v"
    and unique: "\<forall>u. prefix w u \<longrightarrow>
      (pp_t_holds C u \<longleftrightarrow> u = v)"
    using atom unfolding pp_t_atom_at_def by blast
  have "w = v"
    using unique true by simp
  then show ?thesis
    using unique by simp
qed

lemma pp_t_child_atom_at_is_atom:
  assumes child: "pp_t_child_atom_at w Q"
  shows "pp_t_atom_at w Q"
proof -
  obtain b where unique:
      "\<forall>u. prefix w u \<longrightarrow>
        (pp_t_holds Q u \<longleftrightarrow> u = w @ [b])"
    using child unfolding pp_t_child_atom_at_def by blast
  show ?thesis
    unfolding pp_t_atom_at_def
  proof (intro exI[of _ "w @ [b]"] conjI)
    show "prefix w (w @ [b])"
      by simp
  next
    show "\<forall>u. prefix w u \<longrightarrow>
      (pp_t_holds Q u \<longleftrightarrow> u = w @ [b])"
      by (rule unique)
  qed
qed

theorem pp_t_HO_immediate_iff_child_atom:
  assumes C: "Elem C (pp_t_domain Prop)"
    and Q: "Elem Q (pp_t_domain Prop)"
    and C_atom: "pp_t_atom_at w C"
    and C_true: "pp_t_holds C w"
  shows "pp_t_holds
      (((pp_t_closed_den pp_t_HO_immediate_term) \<acute> C)
        \<acute> Q) w
    \<longleftrightarrow> pp_t_child_atom_at w Q"
proof -
  have C_unique:
      "\<forall>u. prefix w u \<longrightarrow>
        (pp_t_holds C u \<longleftrightarrow> u = w)"
    using pp_t_atom_at_true_iff[OF C_atom C_true] .
  have raw:
      "pp_t_holds
        (((pp_t_closed_den pp_t_HO_immediate_term) \<acute> C)
          \<acute> Q) w
      \<longleftrightarrow>
        pp_t_atom_at w Q \<and>
        \<not> pp_t_holds Q w \<and>
        (\<forall>v. prefix w v \<longrightarrow>
          ((\<exists>u. prefix v u \<and> pp_t_holds Q u)
            \<longleftrightarrow>
           pp_t_holds C v \<or> pp_t_holds Q v))"
    using pp_t_HO_immediate_holds[OF C Q, of w] .
  show ?thesis
  proof
    assume immediate:
        "pp_t_holds
          (((pp_t_closed_den pp_t_HO_immediate_term) \<acute> C)
            \<acute> Q) w"
    have conjuncts:
        "pp_t_atom_at w Q \<and>
        \<not> pp_t_holds Q w \<and>
        (\<forall>v. prefix w v \<longrightarrow>
          ((\<exists>u. prefix v u \<and> pp_t_holds Q u)
            \<longleftrightarrow>
           pp_t_holds C v \<or> pp_t_holds Q v))"
      using raw immediate by blast
    have Q_atom: "pp_t_atom_at w Q"
      using conjuncts by blast
    have Q_not_w: "\<not> pp_t_holds Q w"
      using conjuncts by blast
    have diamond:
        "\<forall>v. prefix w v \<longrightarrow>
          ((\<exists>u. prefix v u \<and> pp_t_holds Q u)
            \<longleftrightarrow>
           pp_t_holds C v \<or> pp_t_holds Q v)"
      using conjuncts by blast
    obtain v where v_future: "prefix w v"
      and Q_unique:
        "\<forall>u. prefix w u \<longrightarrow>
          (pp_t_holds Q u \<longleftrightarrow> u = v)"
      using Q_atom unfolding pp_t_atom_at_def by blast
    have v_ne_w: "v \<noteq> w"
      using Q_unique v_future Q_not_w by blast
    have strict: "strict_prefix w v"
      using v_future v_ne_w
      unfolding strict_prefix_def by blast
    then obtain b zs where v_split: "v = w @ b # zs"
      by (rule strict_prefixE')
    let ?q = "w @ [b]"
    have q_future: "prefix w ?q"
      by simp
    have q_v: "prefix ?q v"
      using v_split by (simp add: prefix_def)
    have Q_v: "pp_t_holds Q v"
      using Q_unique v_future by simp
    have possible_at_q:
        "\<exists>u. prefix ?q u \<and> pp_t_holds Q u"
      using q_v Q_v by blast
    have C_or_Q_at_q:
        "pp_t_holds C ?q \<or> pp_t_holds Q ?q"
      using diamond q_future possible_at_q by blast
    have not_C_q: "\<not> pp_t_holds C ?q"
      using C_unique q_future by simp
    have Q_q: "pp_t_holds Q ?q"
      using C_or_Q_at_q not_C_q by blast
    have q_eq_v: "?q = v"
      using Q_unique q_future Q_q by blast
    show "pp_t_child_atom_at w Q"
      unfolding pp_t_child_atom_at_def
      using Q_unique q_eq_v by blast
  next
    assume child: "pp_t_child_atom_at w Q"
    obtain b where Q_unique:
        "\<forall>u. prefix w u \<longrightarrow>
          (pp_t_holds Q u \<longleftrightarrow> u = w @ [b])"
      using child unfolding pp_t_child_atom_at_def by blast
    have Q_atom: "pp_t_atom_at w Q"
      using child by (rule pp_t_child_atom_at_is_atom)
    have Q_not_w: "\<not> pp_t_holds Q w"
      using Q_unique by simp
    have diamond:
        "\<forall>v. prefix w v \<longrightarrow>
          ((\<exists>u. prefix v u \<and> pp_t_holds Q u)
            \<longleftrightarrow>
           pp_t_holds C v \<or> pp_t_holds Q v)"
    proof (intro allI impI)
      fix v
      assume v_future: "prefix w v"
      show "(\<exists>u. prefix v u \<and> pp_t_holds Q u)
          \<longleftrightarrow> pp_t_holds C v \<or> pp_t_holds Q v"
      proof
        assume possible: "\<exists>u. prefix v u \<and> pp_t_holds Q u"
        then obtain u where vu: "prefix v u" and Q_u: "pp_t_holds Q u"
          by blast
        have u_future: "prefix w u"
          using v_future vu by (rule prefix_order.trans)
        have u_child: "u = w @ [b]"
          using Q_unique u_future Q_u by blast
        obtain xs where v: "v = w @ xs"
          using v_future unfolding prefix_def by blast
        have xs_prefix: "prefix xs [b]"
          using vu unfolding v u_child prefix_def by simp
        have xs_length: "length xs \<le> 1"
          using prefix_length_le[OF xs_prefix] by simp
        have "xs = [] \<or> xs = [b]"
        proof (cases xs)
          case Nil
          then show ?thesis by simp
        next
          case (Cons c cs)
          then have "cs = []"
            using xs_length by simp
          moreover have "c = b"
            using xs_prefix Cons calculation
            unfolding prefix_def by auto
          ultimately show ?thesis
            using Cons by simp
        qed
        then have "v = w \<or> v = w @ [b]"
          unfolding v by auto
        then show "pp_t_holds C v \<or> pp_t_holds Q v"
          using C_unique Q_unique v_future by blast
      next
        assume "pp_t_holds C v \<or> pp_t_holds Q v"
        then have "v = w \<or> v = w @ [b]"
          using C_unique Q_unique v_future by blast
        then show "\<exists>u. prefix v u \<and> pp_t_holds Q u"
        proof
          assume "v = w"
          moreover have "prefix w (w @ [b])"
            by simp
          moreover have "pp_t_holds Q (w @ [b])"
            using Q_unique by simp
          ultimately show ?thesis by blast
        next
          assume "v = w @ [b]"
          moreover have "pp_t_holds Q v"
            using Q_unique v_future calculation by simp
          ultimately show ?thesis by blast
        qed
      qed
    qed
    show "pp_t_holds
        (((pp_t_closed_den pp_t_HO_immediate_term) \<acute> C)
          \<acute> Q) w"
      using raw Q_atom Q_not_w diamond by blast
  qed
qed

lemma pp_t_HO_child_xor_raw:
  assumes P: "Elem P (pp_t_domain Prop)"
  shows "pp_t_holds
      ((pp_t_closed_den pp_t_HO_child_xor_term) \<acute> P) w
    \<longleftrightarrow>
      (\<exists>C. Elem C (pp_t_domain Prop) \<and>
        pp_t_holds
          ((pp_t_closed_den pp_t_HO_atom_term) \<acute> C) w \<and>
        pp_t_holds C w \<and>
        (\<exists>Q. Elem Q (pp_t_domain Prop) \<and>
          pp_t_holds
            (((pp_t_closed_den pp_t_HO_immediate_term) \<acute> C)
              \<acute> Q) w \<and>
          (\<forall>v. prefix w v \<longrightarrow>
            (pp_t_holds Q v \<longleftrightarrow>
              (pp_t_holds Q v \<and> pp_t_holds P v)))) \<and>
        (\<exists>Q. Elem Q (pp_t_domain Prop) \<and>
          pp_t_holds
            (((pp_t_closed_den pp_t_HO_immediate_term) \<acute> C)
              \<acute> Q) w \<and>
          (\<forall>v. prefix w v \<longrightarrow>
            (pp_t_holds Q v \<longleftrightarrow>
              (pp_t_holds Q v \<and> \<not> pp_t_holds P v)))))"
  using P
  by (simp add: pp_t_closed_den_def
      pp_t_HO_child_xor_term_def Lambda_app)

lemma pp_t_HO_child_positive_iff:
  assumes C: "Elem C (pp_t_domain Prop)"
    and P: "Elem P (pp_t_domain Prop)"
    and C_atom: "pp_t_atom_at w C"
    and C_true: "pp_t_holds C w"
  shows "(\<exists>Q. Elem Q (pp_t_domain Prop) \<and>
      pp_t_holds
        (((pp_t_closed_den pp_t_HO_immediate_term) \<acute> C)
          \<acute> Q) w \<and>
      (\<forall>v. prefix w v \<longrightarrow>
        (pp_t_holds Q v \<longleftrightarrow>
          (pp_t_holds Q v \<and> pp_t_holds P v))))
    \<longleftrightarrow> (\<exists>b. pp_t_holds P (w @ [b]))"
proof
  assume left:
      "\<exists>Q. Elem Q (pp_t_domain Prop) \<and>
        pp_t_holds
          (((pp_t_closed_den pp_t_HO_immediate_term) \<acute> C)
            \<acute> Q) w \<and>
        (\<forall>v. prefix w v \<longrightarrow>
          (pp_t_holds Q v \<longleftrightarrow>
            (pp_t_holds Q v \<and> pp_t_holds P v)))"
  then obtain Q where Q: "Elem Q (pp_t_domain Prop)"
    and immediate:
      "pp_t_holds
        (((pp_t_closed_den pp_t_HO_immediate_term) \<acute> C)
          \<acute> Q) w"
    and included:
      "\<forall>v. prefix w v \<longrightarrow>
        (pp_t_holds Q v \<longleftrightarrow>
          (pp_t_holds Q v \<and> pp_t_holds P v))"
    by blast
  have child: "pp_t_child_atom_at w Q"
    using pp_t_HO_immediate_iff_child_atom[
      OF C Q C_atom C_true] immediate by blast
  then obtain b where unique:
      "\<forall>v. prefix w v \<longrightarrow>
        (pp_t_holds Q v \<longleftrightarrow> v = w @ [b])"
    unfolding pp_t_child_atom_at_def by blast
  have future: "prefix w (w @ [b])"
    by simp
  have Q_child: "pp_t_holds Q (w @ [b])"
    using unique future by simp
  have P_child: "pp_t_holds P (w @ [b])"
    using included future Q_child by blast
  show "\<exists>b. pp_t_holds P (w @ [b])"
    using P_child by blast
next
  assume right: "\<exists>b. pp_t_holds P (w @ [b])"
  then obtain b where P_child: "pp_t_holds P (w @ [b])"
    by blast
  let ?Q = "pp_zf_of_b {w @ [b]}"
  have Q: "Elem ?Q (pp_t_domain Prop)"
    by (rule pp_zf_of_b_in_domain)
  have child: "pp_t_child_atom_at w ?Q"
    unfolding pp_t_child_atom_at_def
    by (intro exI[of _ b] allI impI) simp
  have immediate:
      "pp_t_holds
        (((pp_t_closed_den pp_t_HO_immediate_term) \<acute> C)
          \<acute> ?Q) w"
    using pp_t_HO_immediate_iff_child_atom[
      OF C Q C_atom C_true] child by blast
  have included:
      "\<forall>v. prefix w v \<longrightarrow>
        (pp_t_holds ?Q v \<longleftrightarrow>
          (pp_t_holds ?Q v \<and> pp_t_holds P v))"
  proof (intro allI impI)
    fix v
    assume "prefix w v"
    show "pp_t_holds ?Q v \<longleftrightarrow>
        (pp_t_holds ?Q v \<and> pp_t_holds P v)"
      using P_child by auto
  qed
  show "\<exists>Q. Elem Q (pp_t_domain Prop) \<and>
      pp_t_holds
        (((pp_t_closed_den pp_t_HO_immediate_term) \<acute> C)
          \<acute> Q) w \<and>
      (\<forall>v. prefix w v \<longrightarrow>
        (pp_t_holds Q v \<longleftrightarrow>
          (pp_t_holds Q v \<and> pp_t_holds P v)))"
    using Q immediate included by blast
qed

lemma pp_t_HO_child_negative_iff:
  assumes C: "Elem C (pp_t_domain Prop)"
    and P: "Elem P (pp_t_domain Prop)"
    and C_atom: "pp_t_atom_at w C"
    and C_true: "pp_t_holds C w"
  shows "(\<exists>Q. Elem Q (pp_t_domain Prop) \<and>
      pp_t_holds
        (((pp_t_closed_den pp_t_HO_immediate_term) \<acute> C)
          \<acute> Q) w \<and>
      (\<forall>v. prefix w v \<longrightarrow>
        (pp_t_holds Q v \<longleftrightarrow>
          (pp_t_holds Q v \<and> \<not> pp_t_holds P v))))
    \<longleftrightarrow> (\<exists>b. \<not> pp_t_holds P (w @ [b]))"
proof
  assume left:
      "\<exists>Q. Elem Q (pp_t_domain Prop) \<and>
        pp_t_holds
          (((pp_t_closed_den pp_t_HO_immediate_term) \<acute> C)
            \<acute> Q) w \<and>
        (\<forall>v. prefix w v \<longrightarrow>
          (pp_t_holds Q v \<longleftrightarrow>
            (pp_t_holds Q v \<and> \<not> pp_t_holds P v)))"
  then obtain Q where Q: "Elem Q (pp_t_domain Prop)"
    and immediate:
      "pp_t_holds
        (((pp_t_closed_den pp_t_HO_immediate_term) \<acute> C)
          \<acute> Q) w"
    and excluded:
      "\<forall>v. prefix w v \<longrightarrow>
        (pp_t_holds Q v \<longleftrightarrow>
          (pp_t_holds Q v \<and> \<not> pp_t_holds P v))"
    by blast
  have child: "pp_t_child_atom_at w Q"
    using pp_t_HO_immediate_iff_child_atom[
      OF C Q C_atom C_true] immediate by blast
  then obtain b where unique:
      "\<forall>v. prefix w v \<longrightarrow>
        (pp_t_holds Q v \<longleftrightarrow> v = w @ [b])"
    unfolding pp_t_child_atom_at_def by blast
  have future: "prefix w (w @ [b])"
    by simp
  have Q_child: "pp_t_holds Q (w @ [b])"
    using unique future by simp
  have not_P_child: "\<not> pp_t_holds P (w @ [b])"
    using excluded future Q_child by blast
  show "\<exists>b. \<not> pp_t_holds P (w @ [b])"
    using not_P_child by blast
next
  assume right: "\<exists>b. \<not> pp_t_holds P (w @ [b])"
  then obtain b where not_P_child:
      "\<not> pp_t_holds P (w @ [b])"
    by blast
  let ?Q = "pp_zf_of_b {w @ [b]}"
  have Q: "Elem ?Q (pp_t_domain Prop)"
    by (rule pp_zf_of_b_in_domain)
  have child: "pp_t_child_atom_at w ?Q"
    unfolding pp_t_child_atom_at_def
    by (intro exI[of _ b] allI impI) simp
  have immediate:
      "pp_t_holds
        (((pp_t_closed_den pp_t_HO_immediate_term) \<acute> C)
          \<acute> ?Q) w"
    using pp_t_HO_immediate_iff_child_atom[
      OF C Q C_atom C_true] child by blast
  have excluded:
      "\<forall>v. prefix w v \<longrightarrow>
        (pp_t_holds ?Q v \<longleftrightarrow>
          (pp_t_holds ?Q v \<and> \<not> pp_t_holds P v))"
  proof (intro allI impI)
    fix v
    assume "prefix w v"
    show "pp_t_holds ?Q v \<longleftrightarrow>
        (pp_t_holds ?Q v \<and> \<not> pp_t_holds P v)"
      using not_P_child by auto
  qed
  show "\<exists>Q. Elem Q (pp_t_domain Prop) \<and>
      pp_t_holds
        (((pp_t_closed_den pp_t_HO_immediate_term) \<acute> C)
          \<acute> Q) w \<and>
      (\<forall>v. prefix w v \<longrightarrow>
        (pp_t_holds Q v \<longleftrightarrow>
          (pp_t_holds Q v \<and> \<not> pp_t_holds P v)))"
    using Q immediate excluded by blast
qed

theorem pp_t_HO_child_xor_holds:
  assumes P: "Elem P (pp_t_domain Prop)"
  shows "pp_t_holds
      ((pp_t_closed_den pp_t_HO_child_xor_term) \<acute> P) w
    \<longleftrightarrow>
      (pp_t_holds P (w @ [False]) \<noteq>
       pp_t_holds P (w @ [True]))"
proof -
  let ?C = "pp_zf_of_b {w}"
  have C: "Elem ?C (pp_t_domain Prop)"
    by (rule pp_zf_of_b_in_domain)
  have C_atom: "pp_t_atom_at w ?C"
    unfolding pp_t_atom_at_def
    by (intro exI[of _ w] conjI allI impI) simp_all
  have C_true: "pp_t_holds ?C w"
    by simp
  have atom_term:
      "pp_t_holds
        ((pp_t_closed_den pp_t_HO_atom_term) \<acute> ?C) w"
    using pp_t_HO_atom_holds[OF C, of w] C_atom by blast
  have existential:
      "pp_t_holds
        ((pp_t_closed_den pp_t_HO_child_xor_term) \<acute> P) w
      \<longleftrightarrow>
        ((\<exists>b. pp_t_holds P (w @ [b])) \<and>
         (\<exists>b. \<not> pp_t_holds P (w @ [b])))"
  proof
    assume term_holds:
        "pp_t_holds
          ((pp_t_closed_den pp_t_HO_child_xor_term) \<acute> P) w"
    obtain C' where C': "Elem C' (pp_t_domain Prop)"
      and C'_atom_term:
        "pp_t_holds
          ((pp_t_closed_den pp_t_HO_atom_term) \<acute> C') w"
      and C'_true: "pp_t_holds C' w"
      and positive:
        "\<exists>Q. Elem Q (pp_t_domain Prop) \<and>
          pp_t_holds
            (((pp_t_closed_den pp_t_HO_immediate_term) \<acute> C')
              \<acute> Q) w \<and>
          (\<forall>v. prefix w v \<longrightarrow>
            (pp_t_holds Q v \<longleftrightarrow>
              (pp_t_holds Q v \<and> pp_t_holds P v)))"
      and negative:
        "\<exists>Q. Elem Q (pp_t_domain Prop) \<and>
          pp_t_holds
            (((pp_t_closed_den pp_t_HO_immediate_term) \<acute> C')
              \<acute> Q) w \<and>
          (\<forall>v. prefix w v \<longrightarrow>
            (pp_t_holds Q v \<longleftrightarrow>
              (pp_t_holds Q v \<and> \<not> pp_t_holds P v)))"
      using pp_t_HO_child_xor_raw[OF P, of w] term_holds by blast
    have C'_atom: "pp_t_atom_at w C'"
      using pp_t_HO_atom_holds[OF C', of w] C'_atom_term by blast
    have pos: "\<exists>b. pp_t_holds P (w @ [b])"
      using pp_t_HO_child_positive_iff[
        OF C' P C'_atom C'_true] positive by blast
    have neg: "\<exists>b. \<not> pp_t_holds P (w @ [b])"
      using pp_t_HO_child_negative_iff[
        OF C' P C'_atom C'_true] negative by blast
    show "(\<exists>b. pp_t_holds P (w @ [b])) \<and>
        (\<exists>b. \<not> pp_t_holds P (w @ [b]))"
      using pos neg by blast
  next
    assume both:
        "(\<exists>b. pp_t_holds P (w @ [b])) \<and>
         (\<exists>b. \<not> pp_t_holds P (w @ [b]))"
    have positive:
        "\<exists>Q. Elem Q (pp_t_domain Prop) \<and>
          pp_t_holds
            (((pp_t_closed_den pp_t_HO_immediate_term) \<acute> ?C)
              \<acute> Q) w \<and>
          (\<forall>v. prefix w v \<longrightarrow>
            (pp_t_holds Q v \<longleftrightarrow>
              (pp_t_holds Q v \<and> pp_t_holds P v)))"
      using pp_t_HO_child_positive_iff[
        OF C P C_atom C_true] both by blast
    have negative:
        "\<exists>Q. Elem Q (pp_t_domain Prop) \<and>
          pp_t_holds
            (((pp_t_closed_den pp_t_HO_immediate_term) \<acute> ?C)
              \<acute> Q) w \<and>
          (\<forall>v. prefix w v \<longrightarrow>
            (pp_t_holds Q v \<longleftrightarrow>
              (pp_t_holds Q v \<and> \<not> pp_t_holds P v)))"
      using pp_t_HO_child_negative_iff[
        OF C P C_atom C_true] both by blast
    have raw_right:
        "\<exists>C. Elem C (pp_t_domain Prop) \<and>
          pp_t_holds
            ((pp_t_closed_den pp_t_HO_atom_term) \<acute> C) w \<and>
          pp_t_holds C w \<and>
          (\<exists>Q. Elem Q (pp_t_domain Prop) \<and>
            pp_t_holds
              (((pp_t_closed_den pp_t_HO_immediate_term) \<acute> C)
                \<acute> Q) w \<and>
            (\<forall>v. prefix w v \<longrightarrow>
              (pp_t_holds Q v \<longleftrightarrow>
                (pp_t_holds Q v \<and> pp_t_holds P v)))) \<and>
          (\<exists>Q. Elem Q (pp_t_domain Prop) \<and>
            pp_t_holds
              (((pp_t_closed_den pp_t_HO_immediate_term) \<acute> C)
                \<acute> Q) w \<and>
            (\<forall>v. prefix w v \<longrightarrow>
              (pp_t_holds Q v \<longleftrightarrow>
                (pp_t_holds Q v \<and> \<not> pp_t_holds P v))))"
      using C atom_term C_true positive negative by blast
    show "pp_t_holds
        ((pp_t_closed_den pp_t_HO_child_xor_term) \<acute> P) w"
      using pp_t_HO_child_xor_raw[OF P, of w] raw_right by blast
  qed
  show ?thesis
    using existential
    by (metis bool.exhaust)
qed

theorem pp_b_operator_of_HO_child_xor:
  "pp_b_operator_of
      (pp_t_closed_den pp_t_HO_child_xor_term) = pp_b_child_xor"
proof (rule ext, rule set_eqI)
  fix P w
  have P_domain: "Elem (pp_zf_of_b P) (pp_t_domain Prop)"
    by (rule pp_zf_of_b_in_domain)
  show "w \<in> pp_b_operator_of
        (pp_t_closed_den pp_t_HO_child_xor_term) P
      \<longleftrightarrow> w \<in> pp_b_child_xor P"
    unfolding pp_b_operator_of_def pp_b_of_zf_def
      pp_b_child_xor_def
    using pp_t_HO_child_xor_holds[OF P_domain, of w]
    by simp
qed

theorem pp_b_child_xor_in_exact_stock:
  "pp_b_child_xor \<in> pp_b_exact_stock"
proof -
  have denotation:
      "pp_b_operator_of
        (pp_t_closed_den pp_t_HO_child_xor_term)
        \<in> pp_b_exact_stock"
    using pp_t_HO_child_xor_terms_typed(3)
      pp_t_HO_child_xor_terms_logical(3)
    by (rule pp_b_exact_stockI)
  show ?thesis
    using denotation pp_b_operator_of_HO_child_xor by simp
qed

subsection \<open>Cancellation and reversibility\<close>

definition pp_b_child_xor_preimage :: pp_b_operator where
  "pp_b_child_xor_preimage S =
    {v @ [False] |v. v \<in> S}"

lemma pp_b_child_xor_preimage_false_child[simp]:
  "w @ [False] \<in> pp_b_child_xor_preimage S \<longleftrightarrow> w \<in> S"
proof
  assume membership:
      "w @ [False] \<in> pp_b_child_xor_preimage S"
  then obtain v where v: "v \<in> S"
    and equality: "w @ [False] = v @ [False]"
    unfolding pp_b_child_xor_preimage_def by blast
  have "w = v"
    using equality by simp
  then show "w \<in> S"
    using v by simp
next
  assume "w \<in> S"
  then show "w @ [False] \<in> pp_b_child_xor_preimage S"
    unfolding pp_b_child_xor_preimage_def by blast
qed

lemma pp_b_child_xor_preimage_true_child[simp]:
  "w @ [True] \<notin> pp_b_child_xor_preimage S"
proof
  assume membership:
      "w @ [True] \<in> pp_b_child_xor_preimage S"
  then obtain v where equality:
      "w @ [True] = v @ [False]"
    unfolding pp_b_child_xor_preimage_def by blast
  have "last (w @ [True]) = last (v @ [False])"
    using arg_cong[OF equality, of last] .
  then show False
    by simp
qed

lemma pp_b_child_xor_preimage_right_inverse:
  "pp_b_child_xor (pp_b_child_xor_preimage S) = S"
  unfolding pp_b_child_xor_def
  by (rule set_eqI) simp

theorem pp_b_child_xor_surjective:
  "surj pp_b_child_xor"
  unfolding surj_def
  using pp_b_child_xor_preimage_right_inverse by blast

lemma pp_b_child_xor_complement:
  "pp_b_child_xor (- P) = pp_b_child_xor P"
  unfolding pp_b_child_xor_def
  by (rule set_eqI) auto

theorem pp_b_child_xor_not_injective:
  "\<not> inj pp_b_child_xor"
proof -
  have same: "pp_b_child_xor {} = pp_b_child_xor UNIV"
    using pp_b_child_xor_complement[of "{}"] by simp
  have distinct: "({} :: pp_b_prop) \<noteq> UNIV"
    by simp
  show ?thesis
    using same distinct unfolding inj_def by blast
qed

corollary pp_b_child_xor_not_bijective:
  "\<not> bij pp_b_child_xor"
  using pp_b_child_xor_not_injective unfolding bij_def by blast

theorem pp_b_exact_child_xor_right_cancellative:
  "pp_b_exact_right_cancellative pp_b_child_xor"
  unfolding pp_b_exact_right_cancellative_def
proof (intro ballI impI)
  fix A B
  assume equality:
      "A \<circ> pp_b_child_xor = B \<circ> pp_b_child_xor"
  show "A = B"
  proof (rule ext)
    fix S
    let ?P = "pp_b_child_xor_preimage S"
    have preimage: "pp_b_child_xor ?P = S"
      by (rule pp_b_child_xor_preimage_right_inverse)
    have at_preimage:
        "A (pp_b_child_xor ?P) = B (pp_b_child_xor ?P)"
      using fun_cong[OF equality, of ?P] by simp
    show "A S = B S"
      using at_preimage preimage by simp
  qed
qed

theorem pp_b_child_xor_not_exact_reversible:
  "\<not> pp_b_exact_reversible pp_b_child_xor"
proof
  assume reversible:
      "pp_b_exact_reversible pp_b_child_xor"
  have inverse_exists:
      "\<exists>W \<in> pp_b_exact_stock.
        pp_b_child_xor \<circ> W = id \<and>
        W \<circ> pp_b_child_xor = id"
    using reversible unfolding pp_b_exact_reversible_def
    by (elim conjE)
  then obtain W where left_inverse:
      "W \<circ> pp_b_child_xor = id"
    by blast
  have at_empty:
      "W (pp_b_child_xor {}) = ({} :: pp_b_prop)"
    using fun_cong[OF left_inverse, of "{}"] by simp
  have at_univ:
      "W (pp_b_child_xor UNIV) = (UNIV :: pp_b_prop)"
    using fun_cong[OF left_inverse, of UNIV] by simp
  have collision:
      "pp_b_child_xor {} = pp_b_child_xor UNIV"
    using pp_b_child_xor_complement[of "{}"] by simp
  have "({} :: pp_b_prop) = UNIV"
    using at_empty at_univ collision by simp
  show False
    using \<open>({} :: pp_b_prop) = UNIV\<close> by simp
qed

corollary pp_b_child_xor_not_in_exact_G:
  "pp_b_child_xor \<notin> pp_b_exact_G"
  using pp_b_child_xor_not_exact_reversible
  unfolding pp_b_exact_G_def by simp

corollary pp_b_child_xor_preserves_fun_prime:
  assumes "pp_b_exact_fun_prime p"
  shows "pp_b_exact_fun_prime (pp_b_child_xor p)"
  using pp_b_exact_fun_prime_image_iff_right_cancellative[
      OF pp_b_child_xor_in_exact_stock assms]
    pp_b_exact_child_xor_right_cancellative
  by blast

theorem pp_b_child_xor_refutes_exact_L2:
  "\<not> pp_b_exact_L2"
  using pp_b_child_xor_in_exact_stock
    pp_b_exact_child_xor_right_cancellative
    pp_b_child_xor_not_in_exact_G
  by (rule pp_b_exact_right_cancellative_nonreversible_refutes_L2)

corollary pp_b_child_xor_refutes_exact_strong_L2:
  "\<not> pp_b_exact_strong_L2"
  using pp_b_child_xor_refutes_exact_L2
    pp_b_exact_strong_L2_imp_L2 by blast

end
