theory Bacon_PP_Goodman_M1
  imports
    Bacon_PP_Goodman_M2
    Bacon_PP_Higher_Bridge
begin

section \<open>Goodman M1: the first failure of PP\<close>

subsection \<open>Purity at the proposition type\<close>

text \<open>
  At the proposition type, the denotations of closed constant-free terms are
  the two invariant propositions.  The corresponding classifier says that a
  proposition's local view is either false or true.  We verify directly that
  this is the familiar non-contingency operator.
\<close>

definition pp_M1_bottom_logical_stock :: "pp_sem_prop set" where
  "pp_M1_bottom_logical_stock = {{}, UNIV}"

definition pp_M1_bottom_purity ::
    "pp_sem_prop \<Rightarrow> pp_sem_prop" where
  "pp_M1_bottom_purity =
    pp_classifier pp_M1_bottom_logical_stock"

lemma pp_M1_bottom_logical_stock_exact:
  "P \<in> pp_M1_bottom_logical_stock
    \<longleftrightarrow> pp_invariant_proposition P"
  unfolding pp_M1_bottom_logical_stock_def
  by (simp add: pp_invariant_proposition_iff_extreme)

theorem pp_M1_bottom_purity_is_noncontingency:
  "pp_M1_bottom_purity = pp_decided"
proof (rule ext, rule set_eqI)
  fix P i
  have "i \<in> pp_M1_bottom_purity P
      \<longleftrightarrow>
      pp_view i P = {} \<or> pp_view i P = UNIV"
    by (simp add: pp_M1_bottom_purity_def
        pp_M1_bottom_logical_stock_def pp_classifier_def)
  also have "... \<longleftrightarrow> i \<in> pp_decided P"
    by (simp add: pp_decided_iff, blast)
  finally show "i \<in> pp_M1_bottom_purity P
      \<longleftrightarrow> i \<in> pp_decided P" .
qed

corollary pp_M1_bottom_purity_modal_form:
  "pp_M1_bottom_purity =
    (\<lambda>P. pp_sem_box P \<union> pp_sem_box (- P))"
proof -
  have "pp_decided =
      (\<lambda>P. pp_sem_box P \<union> pp_sem_box (- P))"
    by (rule ext) (simp add: pp_decided_def)
  then show ?thesis
    using pp_M1_bottom_purity_is_noncontingency by simp
qed

corollary pp_M1_bottom_purity_is_function_space_invariant:
  "pp_function_space_member pp_M1_bottom_purity
    \<and> pp_fun_invariant pp_M1_bottom_purity"
  unfolding pp_M1_bottom_purity_def
  by (rule pp_classifier_is_function_space_invariant)

corollary pp_M1_bottom_purity_in_logical_function_closure:
  "pp_M1_bottom_purity \<in> pp_fclosure G"
  using pp_decided_in_fclosure[of G]
  unfolding pp_M1_bottom_purity_is_noncontingency .

text \<open>
  The last theorem is the semantic denotability certificate: the displayed
  operator is built from identity, negation, necessity, and disjunction in the
  constant-free function closure.  Thus the proposition-type instance of PP
  holds for the intended reason, not merely because the operator is invariant.
\<close>

subsection \<open>The footnote-59 diagonal\<close>

text \<open>
  Bacon's footnote 59 uses only the following abstract structure at the
  proposition and unary-operator types.  The carrier \<open>'p\<close> consists of
  propositions, \<open>true\<close> records actual truth, \<open>Stock\<close> is the certified pure
  unary stock, and \<open>r\<close> is the unique fundamental proposition.  The diagonal
  specification is

  \[
    Dp \quad\longleftrightarrow\quad
    \forall X\in Stock\,(p=Xr\longrightarrow\neg Xp).
  \]

  PP together with Purity of Fun and application closure is what certifies
  this \<open>D\<close> as pure.  Once \<open>D \<in> Stock\<close>, QSS alone supplies the
  contradiction.  Isolating the argument in this form prevents the
  model-theoretic conclusion from depending on any accidental feature of the
  word representation.
\<close>

theorem pp_M1_fn59_diagonal_contradiction:
  fixes Stock :: "('p \<Rightarrow> 'p) set"
    and truth :: "'p \<Rightarrow> bool"
    and r :: 'p
    and D :: "'p \<Rightarrow> 'p"
  assumes D_pure: "D \<in> Stock"
    and qss:
      "\<And>F G. F \<in> Stock \<Longrightarrow> G \<in> Stock \<Longrightarrow>
        F r = G r \<Longrightarrow> F = G"
    and diagonal:
      "\<And>p. truth (D p) =
        (\<forall>X \<in> Stock. p = X r \<longrightarrow> \<not> truth (X p))"
  shows False
proof -
  let ?d = "D r"
  have liar:
      "truth (D ?d) =
        (\<forall>X \<in> Stock. ?d = X r \<longrightarrow> \<not> truth (X ?d))"
    by (rule diagonal)
  have forward: "truth (D ?d) \<Longrightarrow> \<not> truth (D ?d)"
  proof -
    assume true_Dd: "truth (D ?d)"
    have universal:
        "\<forall>X \<in> Stock. ?d = X r \<longrightarrow> \<not> truth (X ?d)"
      using liar true_Dd by simp
    show "\<not> truth (D ?d)"
      using universal D_pure by blast
  qed
  have backward: "\<not> truth (D ?d) \<Longrightarrow> truth (D ?d)"
  proof -
    assume false_Dd: "\<not> truth (D ?d)"
    have universal:
        "\<forall>X \<in> Stock. ?d = X r \<longrightarrow> \<not> truth (X ?d)"
    proof (intro ballI impI)
      fix X
      assume X_pure: "X \<in> Stock"
        and same_value: "?d = X r"
      have "D = X"
        using D_pure X_pure same_value
        by (rule qss)
      then show "\<not> truth (X ?d)"
        using false_Dd by simp
    qed
    show "truth (D ?d)"
      using liar universal by simp
  qed
  show False
    using forward backward by blast
qed

corollary pp_M1_no_pure_fn59_diagonal_under_QSS:
  fixes Stock :: "('p \<Rightarrow> 'p) set"
    and truth :: "'p \<Rightarrow> bool"
    and r :: 'p
    and D :: "'p \<Rightarrow> 'p"
  assumes qss:
      "\<And>F G. F \<in> Stock \<Longrightarrow> G \<in> Stock \<Longrightarrow>
        F r = G r \<Longrightarrow> F = G"
    and diagonal:
      "\<And>p. truth (D p) =
        (\<forall>X \<in> Stock. p = X r \<longrightarrow> \<not> truth (X p))"
  shows "D \<notin> Stock"
proof
  assume "D \<in> Stock"
  then show False
    using qss diagonal
    by (rule pp_M1_fn59_diagonal_contradiction)
qed

text \<open>
  Therefore every Bacon model validating QSS at a fundamental proposition
  must omit the footnote-59 diagonal from its certified pure unary stock.
  In the appendix model, PP at \<open>t \<rightarrow> t\<close> and Purity of Fun would,
  through the constant-free diagonal term, put that operator into the stock.
  Hence PP at that type fails.  The exact closed footnote-59 term, its two
  beta contractions, its derivable purity, and the reduction through unique
  fundamentality are supplied by \<open>Bacon_PP_Goodman_M1_Complete\<close>.
\<close>

end
