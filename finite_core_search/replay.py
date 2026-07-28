from __future__ import annotations

from pathlib import Path

from .axioms import AxiomEntry, Profile
from .prover import ProofNode, SearchResult
from .terms import PROP, Term, Type, infer_type


def _set_literal(formulas: list[Term]) -> str:
    if not formulas:
        return "{}"
    result = "{}"
    for formula in reversed(formulas):
        result = f"insert ({formula.isabelle()}) ({result})"
    return result


def _membership_proof(axiom: AxiomEntry, profile: Profile) -> list[str]:
    formula = axiom.formula
    family = axiom.family
    if family == "pp":
        return [
            "using finite_core_target_PP_in_profile[of "
            f"{profile.isabelle}]",
            "by (simp add: pp_target_PP_def pp_purity_of_pure_def",
            "    pp_pure_def pp_Pure_def pp_pure_name_def)",
        ]
    if family == "unique_fundamental":
        return [
            "using finite_core_unique_fundamental_in_profile[of "
            f"{profile.isabelle}]",
            "by (simp add: pp_unique_fundamental_def pp_fun_def pp_Fun_def",
            "    pp_fun_name_def)",
        ]
    if family == "zeroary_recombination":
        return [
            "using finite_core_zeroary_recombination_in_profile[of "
            f"{profile.isabelle}]",
            "by (simp add: pp_zeroary_recombination_def pp_pure_def",
            "    pp_Pure_def pp_pure_name_def ObjBox_def ObjTrue_def)",
        ]
    if family == "unary_recombination":
        return [
            "using finite_core_unary_recombination_in_profile[of "
            f"{profile.isabelle}]",
            "by (simp add: pp_unary_recombination_def pp_pure_def",
            "    pp_Pure_def pp_pure_name_def pp_fun_def pp_Fun_def",
            "    pp_fun_name_def ObjBox_def ObjTrue_def)",
        ]
    if family == "zeroary_exhaustion":
        return [
            "using finite_core_zeroary_exhaustion_in_profile[of "
            f"{profile.isabelle}]",
            "by (simp add: pp_zeroary_exhaustion_def pp_pure_def",
            "    pp_Pure_def pp_pure_name_def ObjBox_def ObjTrue_def)",
        ]
    if family == "unary_exhaustion":
        return [
            "using finite_core_unary_exhaustion_in_profile[of "
            f"{profile.isabelle}]",
            "by (simp add: pp_unary_exhaustion_def pp_pure_def",
            "    pp_Pure_def pp_pure_name_def pp_fun_def pp_Fun_def",
            "    pp_fun_name_def ObjBox_def ObjTrue_def)",
        ]
    if family == "purity":
        assert axiom.source_type is not None
        term = formula.args[1]
        return [
            "proof -",
            "  have raw:",
            f"    \"pp_pure ({axiom.source_type.isabelle()}) "
            f"({term.isabelle()})",
            f"      \\<in> finite_core_profile_axioms {profile.isabelle}\"",
            "  proof (rule finite_core_purity_in_profile,",
            "      rule finite_core_purity_schemaI)",
            f"    show \"infer_type [] ({term.isabelle()}) = "
            f"Some ({axiom.source_type.isabelle()})\"",
            "      by (simp add: lookup_def)",
            f"    show \"consts_of ({term.isabelle()}) = {{}}\" by simp",
            "  qed",
            "  show ?thesis",
            "    using raw by (simp add: pp_pure_def pp_Pure_def",
            "      pp_pure_name_def)",
            "qed",
        ]
    if family == "application_closure":
        arrow = formula.args[0]
        assert isinstance(arrow, Type) and arrow.tag == "Arr"
        assert arrow.left is not None and arrow.right is not None
        return [
            "using finite_core_application_closure_in_profile[of",
            f"      \"{arrow.left.isabelle()}\"",
            f"      \"{arrow.right.isabelle()}\"",
            f"      {profile.isabelle}]",
            "by (simp add: pp_application_closure_def pp_pure_def",
            "    pp_Pure_def pp_pure_name_def)",
        ]
    if family == "no_fundamentals":
        sigma = formula.args[0]
        assert isinstance(sigma, Type)
        return [
            "using finite_core_no_fundamentals_in_profile[of",
            f"      \"{sigma.isabelle()}\" {profile.isabelle}]",
            "by (simp add: pp_no_fundamentals_def pp_fun_def pp_Fun_def",
            "    pp_fun_name_def)",
        ]
    if family == "modalized_functionality":
        arrow = formula.args[0]
        assert isinstance(arrow, Type) and arrow.tag == "Arr"
        assert arrow.left is not None and arrow.right is not None
        return [
            "using finite_core_modalized_functionality_in_profile[of",
            f"      {profile.isabelle}",
            f"      \"{arrow.left.isabelle()}\"",
            f"      \"{arrow.right.isabelle()}\"]",
            "by (simp add: fresh_modalized_functionality_def ObjBox_def",
            "    ObjTrue_def)",
        ]
    raise ValueError(f"no membership replay for family {family}")


def _proof_step(
    index: int,
    node: ProofNode,
    names: dict[Term, str],
) -> list[str]:
    name = f"d{index}"
    formula = node.conclusion.isabelle()
    target = (
        f'lemma {name}: "[] ; finite_core_axioms '
        f'\\<turnstile>\\<^sub>CEV\\<^sup>+ ({formula})"'
    )
    lines = [target]
    if node.rule == "axiom":
        lines.extend(
            [
                "proof (rule CEV_axiom_proves.Axiom)",
                f"  show \"({formula}) \\<in> finite_core_axioms\"",
                "    by (simp add: finite_core_axioms_def)",
                f"  show \"[] \\<turnstile> ({formula}) : Prop\"",
                "    by (rule infer_type_sound) simp",
                "qed",
            ]
        )
    elif node.rule == "obj_true":
        lines.append("  by (rule finite_core_ObjTrue)")
    elif node.rule == "ref":
        assert node.witness is not None
        witness_ty = infer_type((), node.witness)
        assert witness_ty is not None
        lines.extend(
            [
                "proof (rule finite_core_reflexivity)",
                f"  show \"[] \\<turnstile> ({node.witness.isabelle()}) : "
                f"{witness_ty.isabelle()}\"",
                "    by (rule infer_type_sound) simp",
                "qed",
            ]
        )
    elif node.rule in {"conj_left", "conj_right", "double_negation"}:
        lemma = {
            "conj_left": "finite_core_conj_left",
            "conj_right": "finite_core_conj_right",
            "double_negation": "finite_core_double_negation",
        }[node.rule]
        lines.append(f"  using {names[node.premises[0]]} by (rule {lemma})")
    elif node.rule == "mp":
        lines.append(
            f"  using {names[node.premises[0]]} "
            f"{names[node.premises[1]]} by (rule CEV_axiom_proves.MP)"
        )
    elif node.rule == "conj_intro":
        lines.append(
            f"  using {names[node.premises[0]]} "
            f"{names[node.premises[1]]} by (rule CEV_axiom_conj_intro)"
        )
    elif node.rule == "contradiction":
        lines.append(
            f"  using {names[node.premises[0]]} "
            f"{names[node.premises[1]]} by (rule finite_core_contradiction)"
        )
    elif node.rule == "forall_elim":
        assert node.witness is not None
        universal = node.premises[0]
        assert universal.tag == "Forall"
        sigma, _ = universal.args
        witness_ty = infer_type((), node.witness)
        assert witness_ty == sigma
        lines.extend(
            [
                "proof (rule CEV_axiom_UI_typed)",
                f"  show \"[] \\<turnstile> ({universal.isabelle()}) : Prop\"",
                "    by (rule infer_type_sound) simp",
                f"  show \"[] \\<turnstile> ({node.witness.isabelle()}) : "
                f"{sigma.isabelle()}\"",
                "    by (rule infer_type_sound) simp",
                f"  show \"[] ; finite_core_axioms "
                f"\\<turnstile>\\<^sub>CEV\\<^sup>+ "
                f"({universal.isabelle()})\"",
                f"    using {names[universal]} .",
                "qed",
            ]
        )
    elif node.rule == "prop_equivalence":
        biconditional = node.premises[0]
        assert biconditional.tag == "Conj"
        left = biconditional.args[0].args[0]
        right = biconditional.args[0].args[1]
        lines.extend(
            [
                "proof (rule CEV_axiom_zeroary_equivalence)",
                f"  show \"[] \\<turnstile> ({left.isabelle()}) : Prop\"",
                "    by (rule infer_type_sound) simp",
                f"  show \"[] \\<turnstile> ({right.isabelle()}) : Prop\"",
                "    by (rule infer_type_sound) simp",
                f"  show \"[] ; finite_core_axioms "
                f"\\<turnstile>\\<^sub>CEV\\<^sup>+ "
                f"({biconditional.isabelle()})\"",
                f"    using {names[biconditional]} .",
                "qed",
            ]
        )
    else:
        raise ValueError(f"no replay rule for {node.rule}")
    return lines


def emit_replay(
    output_dir: Path,
    profile: Profile,
    core: list[AxiomEntry],
    result: SearchResult,
    session_name: str = "Goodman_Finite_Core_Replay",
) -> tuple[Path, Path]:
    if not result.found:
        raise ValueError("cannot emit a contradiction replay without a proof")
    output_dir.mkdir(parents=True, exist_ok=True)
    theory_path = output_dir / "Finite_Core_Replay.thy"
    root_path = output_dir / "ROOT"
    dag = result.proof_dag()
    names: dict[Term, str] = {}
    proof_lines: list[str] = []
    for index, node in enumerate(dag):
        proof_lines.extend(_proof_step(index, node, names))
        proof_lines.append("")
        names[node.conclusion] = f"d{index}"

    membership_lines: list[str] = []
    membership_names: list[str] = []
    for index, axiom in enumerate(core):
        member_name = f"member_{index}"
        membership_names.append(member_name)
        membership_lines.append(
            f'lemma {member_name}: "({axiom.formula.isabelle()}) '
            f'\\<in> finite_core_profile_axioms {profile.isabelle}"'
        )
        membership_lines.extend(_membership_proof(axiom, profile))
        membership_lines.append("")

    core_literal = _set_literal([axiom.formula for axiom in core])
    final_derivation_name = names[result.false_proof.conclusion]
    theory = "\n".join(
        [
            "theory Finite_Core_Replay",
            "  imports Goodman_CEVplus_Canonical.Bacon_PP_Fresh_Finite_Core_Search",
            "begin",
            "",
            "text \\<open>",
            "  This file was generated by finite_core_search.  Its final",
            "  theorem is accepted as a finite inconsistent core only if this",
            "  theory builds and the theorem-object audit below is clean.",
            "\\<close>",
            "",
            "definition finite_core_axioms :: \"oterm set\" where",
            f'  "finite_core_axioms = {core_literal}"',
            "",
            *membership_lines,
            "lemma finite_core_axioms_subset:",
            f'  "finite_core_axioms \\<subseteq> '
            f'finite_core_profile_axioms {profile.isabelle}"',
            "  unfolding finite_core_axioms_def",
            f"  using {' '.join(membership_names)} by blast",
            "",
            *proof_lines,
            "theorem finite_core_derives_false:",
            '  "[] ; finite_core_axioms '
            '\\<turnstile>\\<^sub>CEV\\<^sup>+ ObjFalse"',
            f"  using {final_derivation_name} by (simp add: ObjFalse_def)",
            "",
            "theorem certified_finite_inconsistent_core:",
            f'  "finite_core_certified {profile.isabelle} '
            'finite_core_axioms"',
            "  unfolding finite_core_certified_def",
            "  using finite_core_axioms_subset finite_core_derives_false",
            "  by (simp add: finite_core_axioms_def)",
            "",
            "theorem selected_profile_is_inconsistent:",
            '  "\\<not> CEV_axiom_consistent []',
            f'    (finite_core_profile_axioms {profile.isabelle})"',
            "  using certified_finite_inconsistent_core",
            "  by (rule finite_core_certified_negative_answer)",
            "",
            "ML \\<open>",
            "val target = @{thm selected_profile_is_inconsistent}",
            "val oracles = Thm_Deps.all_oracles [target]",
            "val hyps = Thm.hyps_of target",
            "val tpairs = Thm.tpairs_of target",
            "val _ =",
            "  if null oracles andalso null hyps andalso null tpairs",
            "  then writeln \"FINITE-CORE-REPLAY-CLEAN\"",
            "  else error \"FINITE-CORE-REPLAY-NOT-CLEAN\"",
            "\\<close>",
            "",
            "end",
            "",
        ]
    )
    theory_path.write_text(theory)
    root_path.write_text(
        "\n".join(
            [
                f"session {session_name} = Goodman_CEVplus_Canonical +",
                "  options [timeout = 120]",
                "  theories",
                "    Finite_Core_Replay",
                "",
            ]
        )
    )
    return theory_path, root_path


def emit_manifest_audit(
    output_dir: Path,
    profile: Profile,
    pool: list[AxiomEntry],
    session_name: str = "Goodman_Finite_Core_Manifest_Audit",
) -> tuple[Path, Path]:
    output_dir.mkdir(parents=True, exist_ok=True)
    theory_path = output_dir / "Finite_Core_Manifest_Audit.thy"
    root_path = output_dir / "ROOT"
    membership_lines: list[str] = []
    membership_names: list[str] = []
    for index, axiom in enumerate(pool):
        member_name = f"manifest_member_{index}"
        membership_names.append(member_name)
        membership_lines.append(
            f'lemma {member_name}: "({axiom.formula.isabelle()}) '
            f'\\<in> finite_core_profile_axioms {profile.isabelle}"'
        )
        membership_lines.extend(_membership_proof(axiom, profile))
        membership_lines.append("")
    target_chunks = [
        "  " + ", ".join(
            f"@{{thm {name}}}" for name in membership_names[index:index + 12]
        )
        for index in range(0, len(membership_names), 12)
    ]
    target_lines: list[str] = []
    for index, chunk in enumerate(target_chunks):
        prefix = "[" if index == 0 else " "
        suffix = "]" if index == len(target_chunks) - 1 else ","
        target_lines.append(prefix + chunk + suffix)
    theory_path.write_text(
        "\n".join(
            [
                "theory Finite_Core_Manifest_Audit",
                "  imports Goodman_CEVplus_Canonical.Bacon_PP_Fresh_Finite_Core_Search",
                "begin",
                "",
                *membership_lines,
                "ML \\<open>",
                "val targets =",
                *target_lines,
                "val oracles = maps (fn th => Thm_Deps.all_oracles [th]) targets",
                "val hyps = maps Thm.hyps_of targets",
                "val tpairs = maps Thm.tpairs_of targets",
                "val _ =",
                "  if null oracles andalso null hyps andalso null tpairs",
                "  then writeln (\"FINITE-CORE-MANIFEST-CLEAN: \" ^",
                "    Int.toString (length targets) ^ \" members\")",
                "  else error \"FINITE-CORE-MANIFEST-NOT-CLEAN\"",
                "\\<close>",
                "",
                "end",
                "",
            ]
        )
    )
    root_path.write_text(
        "\n".join(
            [
                f"session {session_name} = Goodman_CEVplus_Canonical +",
                "  options [timeout = 900]",
                "  theories",
                "    Finite_Core_Manifest_Audit",
                "",
            ]
        )
    )
    return theory_path, root_path
