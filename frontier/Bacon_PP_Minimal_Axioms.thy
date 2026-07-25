theory Bacon_PP_Minimal_Axioms
  imports "Higher_Order_Metaphysics_PP.Bacon_PP_Diagonal"
begin

section \<open>Trimming the axiom set: zeroary Recombination is redundant\<close>

text \<open>
  When the problem is stated as ``is \<open>X\<close> consistent with the background logic plus
  assumptions \<open>A\<close>'', \<open>A\<close> should be minimal --- an assumption that the background logic
  already proves is not an assumption.  \<open>pp_zeroary_recombination\<close> is such a case.  It
  says \<open>\<forall>p. Pure p \<longrightarrow> (\<box>p \<longrightarrow> p)\<close>, but CEV proves the modal \<open>T\<close> schema \<open>\<box>A \<longrightarrow> A\<close> for
  \emph{every} \<open>A\<close> (\<open>CEV_modal_T\<close>), so the purity restriction is idle.
\<close>

theorem CEV_proves_zeroary_recombination:
  "[] \<turnstile>\<^sub>CEV pp_zeroary_recombination"
proof -
  let ?p = "Var 0 :: oterm"
  let ?X = "Imp (\<box>\<^sub>o ?p) ?p"
  let ?Q = "Imp (pp_pure Prop ?p) ?X"
  have p_type: "[Prop] \<turnstile> ?p : Prop"
    by (rule has_type.Var) (simp add: lookup_def)
  have X_type: "[Prop] \<turnstile> ?X : Prop"
    using p_type by (intro has_type.Imp typed_ObjBox)
  have pure_type: "[Prop] \<turnstile> pp_pure Prop ?p : Prop"
    using p_type by (rule typed_pp_pure)
  have Q_type: "[Prop] \<turnstile> ?Q : Prop"
    using pure_type X_type by (rule has_type.Imp)
  have true_type: "[] \<turnstile> ObjTrue : Prop"
    by (rule typed_ObjTrue)

  text \<open>Modal \<open>T\<close>, unrestricted.\<close>
  have d_X: "[Prop] \<turnstile>\<^sub>CEV ?X"
    using CEV_modal_T[OF p_type] by (simp add: modal_T_def)

  text \<open>Weaken by the idle purity antecedent.\<close>
  have d_Q: "[Prop] \<turnstile>\<^sub>CEV ?Q"
    using d_X CEV_taut_imp[OF X_type pure_type]
    by (rule CEV_proves.MP)

  text \<open>Weaken again, to fit the shape of \<open>Gen\<close>.\<close>
  have shift_true: "shift ObjTrue = (ObjTrue :: oterm)"
    by (simp add: ObjTrue_def shift_def)
  have d_imp: "[Prop] \<turnstile>\<^sub>CEV Imp (shift ObjTrue) ?Q"
  proof -
    have "[Prop] \<turnstile> ObjTrue : Prop" by (rule typed_ObjTrue)
    then have "[Prop] \<turnstile>\<^sub>CEV Imp ObjTrue ?Q"
      using d_Q CEV_taut_imp[OF Q_type] by (blast intro: CEV_proves.MP)
    then show ?thesis by (simp add: shift_true)
  qed

  text \<open>Generalise, then discharge \<open>ObjTrue\<close>.\<close>
  have d_gen: "[] \<turnstile>\<^sub>CEV Imp ObjTrue (Forall Prop ?Q)"
    using true_type Q_type d_imp by (rule CEV_proves.Gen)
  have d_true: "[] \<turnstile>\<^sub>CEV ObjTrue"
    by (rule CEV_proves.CE, rule CE_proves.C, rule C_proves.H)
      (rule H_proves_ObjTrue)
  have "[] \<turnstile>\<^sub>CEV Forall Prop ?Q"
    using d_true d_gen by (rule CEV_proves.MP)
  then show ?thesis
    by (simp add: pp_zeroary_recombination_def)
qed

text \<open>
  So the assumption list may drop it.  The remaining members of
  \<open>pp_recombination_background_axioms\<close> --- the purity schema, application closure,
  unique fundamentality at \<open>Prop\<close>, no fundamentals elsewhere, and \emph{unary}
  Recombination --- are not known to be redundant, and unary Recombination certainly is
  not: it is the whole content of the problem.
\<close>

end
