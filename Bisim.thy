theory Bisim
  imports Silent
begin

section \<open>Equivalence Up To Tau\<close>

text \<open>
Similar to prior work, we introduce a notion of equivalence over itrees,
permitting a finite difference in Taus between the two terms.
Additionally, we extend the equivalence to consider an arbitrary relation
over the itrees' results.

To encode this, we first introduce an inductive relation that extends an existing
itree relation to permit some finite difference in Taus. We then take the greatest
fixed point of this relation, permitting a finite difference in taus over infinite
itrees.
\<close>

inductive euttF
  for r :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
  and sim :: "('a,'i,'o) itree \<Rightarrow> ('b,'i,'o) itree \<Rightarrow> bool"
  where
  euttF_RetI[intro]: "r a b \<Longrightarrow> euttF r sim (Ret a) (Ret b)" |
  euttF_IOI[intro]:  "\<forall>v. sim (k1 v) (k2 v) \<Longrightarrow> euttF r sim (IO e k1) (IO e k2)" |
  euttF_TauI[intro]: "sim k1 k2 \<Longrightarrow> euttF r sim (Tau k1) (Tau k2)" |
  euttF_LTI[intro]: "euttF r sim k1 k2 \<Longrightarrow> euttF r sim (Tau k1) k2" |
  euttF_RTI[intro]: "euttF r sim k1 k2 \<Longrightarrow> euttF r sim k1 (Tau k2)"
inductive_cases euttFE: "euttF r S a b"

definition eutt (infix "\<approx>\<index>" 51)
  where "eutt r t t' = gfp (euttF r) t t'"

text \<open>
We specialise @{term eutt} with equivalence over the return values.
\<close>
abbreviation eutt_eq (infix "\<cong>" 51)
  where "eutt_eq t t' \<equiv> eutt (=) t t'"

subsection \<open>Monotone\<close>

lemma euttF_mono_helper:
  "euttF r x a b \<Longrightarrow> \<forall>a b. x a b \<longrightarrow> y a b \<Longrightarrow> euttF r y a b"
  by (induct rule: euttF.induct) (auto)

lemma euttF_mono [mono]:
  "mono (euttF r)"
  by (blast intro: monoI euttF_mono_helper)

lemma eutt_peel:
  "(\<approx>\<^bsub>r\<^esub>) \<equiv> euttF r (gfp (euttF r))"
  unfolding gfp_fixpoint[OF euttF_mono] eutt_def .

subsection \<open>Reflexive\<close>

lemma euttF_refl [intro]:
  assumes "\<forall>b. r b b" "\<forall>b. S b b"
  shows "euttF r S a a"
proof -
  have "euttF r (=) a a" using assms by (cases a) (auto)
  thus ?thesis using assms(2) by (simp add: euttF_mono_helper)
qed

lemma eutt_refl [intro]:
  assumes "\<forall>b. d b b"
  shows "a \<approx>\<^bsub>d\<^esub> a"
proof -
  have "(=) \<le> euttF d (=)" using assms by auto
  hence "(=) \<le> gfp (euttF d)" using gfp_upperbound by blast
  thus ?thesis by (auto simp: eutt_def)
qed

lemma [simp]:
  "x \<cong> x"
  by (rule eutt_refl) auto

subsection \<open>Symmetric\<close>

definition flip
  where "flip f \<equiv> \<lambda>a b. f b a"

lemma flip_elim [simp]:
  "flip (flip f) = f"
  by (auto simp: flip_def)

lemma flip_sym [simp]:
  "symp f \<Longrightarrow> flip f = f"
  by (auto simp: flip_def symp_def)

lemma flip_mono[mono,intro]:
  "mono flip"
  by (auto simp: flip_def le_fun_def intro!: monoI)

lemma euttF_flip:
  assumes "euttF r S a b"
  shows "euttF (flip r) (flip S) b a"
  using assms by (induct) (auto simp: flip_def)

lemma euttF_flip_dist:
  "flip (euttF r S) = euttF (flip r) (flip S)"
proof -
  have "flip (euttF r S) \<le> euttF (flip r) (flip S)"
    using euttF_flip unfolding flip_def by auto
  moreover have "euttF (flip r) (flip S) \<le> flip (euttF r S)"
    using euttF_flip unfolding flip_def by auto
  ultimately show ?thesis by blast
qed

lemma gfp_roll_flip:
  assumes "mono S"
  shows "flip (gfp S) = gfp (\<lambda>f. flip (S (flip f)))"
proof -
  have "flip (gfp (\<lambda>x. (S \<circ> flip) (flip x))) = gfp (\<lambda>x. flip ((S \<circ> flip) x))"
  proof (rule gfp_rolling[OF flip_mono])
    show "mono (S \<circ> flip)" using flip_mono assms monotone_on_o by blast
  qed
  thus ?thesis by (auto simp: comp_def)
qed

lemma eutt_flip_dist:
  "flip (\<lambda>a b. a \<approx>\<^bsub>d\<^esub> b) a b = a \<approx>\<^bsub>flip d\<^esub> b"
  unfolding eutt_def gfp_roll_flip[OF euttF_mono] euttF_flip_dist by auto

lemma eutt_flip:
  assumes "a \<approx>\<^bsub>d\<^esub> b" 
  shows "b \<approx>\<^bsub>flip d\<^esub> a"
  using eutt_flip_dist assms by (auto simp: flip_def)

lemma eutt_sym:
  assumes "symp d" "a \<approx>\<^bsub>d\<^esub> b"
  shows "b \<approx>\<^bsub>d\<^esub> a"
  using eutt_flip assms by force

lemma eutt_eq_sym [intro,sym]:
  assumes "x \<cong> z" shows "z \<cong> x"
  using eutt_sym[OF _ assms] by (auto simp: symp_def)

subsection \<open>Inductive Rules\<close>

lemma eutt_ret_ind [consumes 1, case_names ret sil]:
  assumes "a \<cong> Ret r"
  assumes "P (Ret r)"
  assumes "\<And>t. P t \<Longrightarrow> P (Tau t)"
  shows "P a"
  using assms(1,2,3) unfolding eutt_peel
  by (induct a "Ret r :: ('a, 'b, 'c) itree" arbitrary: r) auto

lemma eutt_io_ind [consumes 1, case_names io sil]:
  assumes "a \<cong> IO e f"
  assumes "\<And>f'. \<forall>v. f' v \<cong> f v \<Longrightarrow> P (IO e f')"
  assumes "\<And>t. P t \<Longrightarrow> P (Tau t)"
  shows "P a"
  using assms(1,2,3) unfolding eutt_peel
  by (induct a "IO e f :: ('a, 'b, 'c) itree" arbitrary: e f) 
     (auto simp add: euttF_mono gfp_fixpoint)

subsection \<open>Finite Tau Prefix\<close>

lemma euttF_tausLI [intro]:
  assumes "l \<leadsto> l'" "euttF d S l' r"
  shows "euttF d S l r"
  using assms by (induct) auto

lemma euttF_tausRI [intro]:
  assumes "r \<leadsto> r'" "euttF d S l r'"
  shows "euttF d S l r"
  using assms by (induct) auto

lemma eutt_tausLI [intro]:
  assumes "l \<leadsto> l'" "l' \<approx>\<^bsub>d\<^esub> r"
  shows "l \<approx>\<^bsub>d\<^esub> r"
  using euttF_tausLI eutt_peel assms by metis

lemma eutt_tausRI [intro]:
  assumes "r \<leadsto> r'" "l \<approx>\<^bsub>d\<^esub> r'"
  shows "l \<approx>\<^bsub>d\<^esub> r"
  using euttF_tausRI eutt_peel assms by metis

lemma tp_eutt [intro]:
  assumes "a \<leadsto> b"
  shows "a \<cong> b"
  using assms by induct auto

subsection \<open>Silent Program\<close>

lemma [elim!]:
  assumes "Ret r \<approx>\<^bsub>d\<^esub> silent"
  obtains "False"
  using assms unfolding eutt_peel
  by (induct "Ret r :: ('a, 'c, 'd) itree" "silent :: ('b, 'c, 'd) itree") auto

lemma [elim!]:
  assumes "IO e f \<approx>\<^bsub>d\<^esub> silent"
  obtains "False"
  using assms unfolding eutt_peel
  by (induct "IO e f :: ('a, 'c, 'd) itree" "silent :: ('b, 'c, 'd) itree") auto

lemma [elim!]:
  assumes "Tau k \<approx>\<^bsub>d\<^esub> silent"
  obtains "k \<approx>\<^bsub>d\<^esub> silent"
  using assms unfolding eutt_peel
proof (induct "Tau k :: ('a, 'c, 'd) itree" "silent :: ('b, 'c, 'd) itree" arbitrary: k)
  case (euttF_TauI k1 k2)
  then show ?case by auto (metis eutt_def eutt_peel)
next
  case (euttF_RTI k2)
  then show ?case by auto
qed

lemma eutt_silentE:
  assumes "k \<approx>\<^bsub>d\<^esub> silent"
  shows "k = silent"
  using assms by (coinduction arbitrary: k) auto

lemma euttF_silentI [intro]:
  assumes "S silent silent"
  shows "euttF d S silent silent"
proof -
  have "euttF d S (Tau silent) (Tau silent)" using assms by auto
  thus ?thesis by (auto simp: silent_fp)
qed

lemma eutt_silentI [intro]:
  shows "silent \<approx>\<^bsub>d\<^esub> silent"
proof -
  let ?P = "\<lambda>a b. a = silent \<and> b = silent"
  have "?P \<le> euttF d ?P" by auto
  hence "?P \<le> gfp (euttF d)" using gfp_upperbound by blast
  thus ?thesis by (auto simp: eutt_def)
qed

lemma eutt_silent [simp]:
  "(k \<approx>\<^bsub>d\<^esub> silent) = (k = silent)"
  by (auto elim: eutt_silentE)

lemma eutt_silent_rev [simp]:
  "(silent \<approx>\<^bsub>d2\<^esub> k2) = (k2 = silent)"
  using eutt_flip eutt_silent by blast

lemma euttF_silentLI [intro]:
  assumes "S silent k"
  shows "euttF r S silent (Tau k)"
  using assms by (subst silent.code) auto

lemma euttF_silentRI [intro]:
  assumes "S k silent"
  shows "euttF r S (Tau k) silent"
  using assms by (subst silent.code) auto

subsection \<open>Elimination Rules\<close>

named_theorems euttF_elims

lemma euttF_RetLE [euttF_elims]:
  assumes "euttF d S (Ret v) b"
  obtains v' where "b \<leadsto> Ret v'" "d v v'"
  using assms by (induct "Ret v :: ('a, 'c, 'd) itree" b) (blast)+

lemma euttF_TauLE [euttF_elims]:
  assumes "euttF d S (Tau l) b"
  obtains r where "b \<leadsto> r" "S l r" | "euttF d S l b"
  using assms by (induct "Tau l :: ('a, 'c, 'd) itree" b) (blast)+

lemma euttF_IOLE [euttF_elims]:
  assumes "euttF d S (IO e f) b"
  obtains f' where "b \<leadsto> IO e f'" "\<forall>v. S (f v) (f' v)"
  using assms by (induct "IO e f :: ('a, 'c, 'd) itree" b) (blast)+

lemma euttF_RetRE [euttF_elims]:
  assumes "euttF d S b (Ret v')"
  obtains v where "b \<leadsto> Ret v" "d v v'"
  using assms by (induct b "Ret v' :: ('b, 'c, 'd) itree") (blast)+

lemma euttF_TauRE [euttF_elims]:
  assumes "euttF d S b (Tau l)"
  obtains r where "b \<leadsto> r" "S r l" | "euttF d S b l"
  using assms by (induct b "Tau l :: ('b, 'c, 'd) itree") (blast)+

lemma euttF_IORE [euttF_elims]:
  assumes "euttF d S b (IO e f)"
  obtains f' where "b \<leadsto> IO e f'" "\<forall>v. S (f' v) (f v)"
  using assms by (induct b "IO e f :: ('b, 'c, 'd) itree") (blast)+

named_theorems eutt_elims

lemma eutt_RetLE[eutt_elims]:
  assumes "Ret v \<approx>\<^bsub>d\<^esub> b"
  obtains v' where "b \<leadsto> Ret v'" "d v v'"
  using euttF_RetLE eutt_def gfp_fixpoint[OF euttF_mono] assms by metis

lemma eutt_TauLE [eutt_elims]:
  assumes "Tau l \<approx>\<^bsub>d\<^esub> b"
  obtains "l \<approx>\<^bsub>d\<^esub> b"
  using assms euttF_TauLE eutt_peel  
  by (metis (no_types, opaque_lifting) eutt_def eutt_tausRI that)

lemma eutt_IOLE[eutt_elims]:
  assumes "IO e f \<approx>\<^bsub>d\<^esub> b"
  obtains f' where "b \<leadsto> IO e f'" "\<forall>v. (f v) \<approx>\<^bsub>d\<^esub> (f' v)"
  using euttF_IOLE eutt_def gfp_fixpoint[OF euttF_mono] assms by metis

lemma eutt_RetRE[eutt_elims]:
  assumes "b \<approx>\<^bsub>d\<^esub> Ret v"
  obtains v' where "b \<leadsto> Ret v'" "d v' v"
  using euttF_RetRE eutt_def gfp_fixpoint[OF euttF_mono] assms by metis

lemma eutt_TauRE[eutt_elims]:
  assumes "b \<approx>\<^bsub>d\<^esub> Tau r"
  obtains "b \<approx>\<^bsub>d\<^esub> r"
  using assms euttF_TauRE eutt_peel  
  by (metis (no_types, opaque_lifting) eutt_def eutt_tausLI that)

lemma eutt_IORE[eutt_elims]:
  assumes "b \<approx>\<^bsub>d\<^esub> IO e f"
  obtains f' where "b \<leadsto> IO e f'"  "\<forall>v. (f' v) \<approx>\<^bsub>d\<^esub> (f v)"
  using euttF_IORE eutt_def gfp_fixpoint[OF euttF_mono] assms by metis

lemma eutt_TausRE:
  assumes "a \<approx>\<^bsub>d\<^esub> b" "b \<leadsto> c"
  obtains "a \<approx>\<^bsub>d\<^esub> c"
  using assms(2,1) by (induct) (auto elim: eutt_TauRE)

lemma eutt_TausLE:
  assumes "a \<approx>\<^bsub>d\<^esub> b" "a \<leadsto> c"
  obtains "c \<approx>\<^bsub>d\<^esub> b"
  using assms(2,1) by (induct) (auto elim: eutt_TauLE)

subsection \<open>Introduction Rules\<close>

lemma eutt_tauLI [intro]:
  assumes "t \<approx>\<^bsub>d\<^esub> t'"
  shows "Tau t \<approx>\<^bsub>d\<^esub> t'"
  using assms unfolding eutt_peel by auto

lemma eutt_tauRI [intro]:
  assumes "t \<approx>\<^bsub>d\<^esub> t'"
  shows "t \<approx>\<^bsub>d\<^esub> Tau t'"
  using assms unfolding eutt_peel by auto

lemma eutt_tauI [intro]:
  assumes "t \<approx>\<^bsub>d\<^esub> t'"
  shows "Tau t \<approx>\<^bsub>d\<^esub> Tau t'"
  using assms unfolding eutt_peel by auto

lemma eutt_ioI [intro]:
  assumes "\<forall>v. t v \<approx>\<^bsub>d\<^esub> t' v"
  shows "IO e t \<approx>\<^bsub>d\<^esub> IO e t'"
  using assms unfolding eutt_peel 
  by (intro euttF.intros, simp add: gfp_fixpoint[OF euttF_mono])

lemma eutt_retI [intro]:
  assumes "d a b"
  shows "Ret a \<approx>\<^bsub>d\<^esub> Ret b"
  using assms unfolding eutt_peel by auto

subsection \<open>Coinduction\<close>

lemma eutt_fp[consumes 1, case_names fp]:
  assumes "P a b" 
  assumes "\<And>a b. P a b \<Longrightarrow> euttF d (\<lambda>a b. (\<exists>a' b'. a \<leadsto> a' \<and> b \<leadsto> b' \<and> P a' b') \<or> a \<approx>\<^bsub>d\<^esub> b) a b"
              (is "\<And>a b. P a b \<Longrightarrow> euttF d (\<lambda>a b. ?P a b \<or> a \<approx>\<^bsub>d\<^esub> b) a b")
  shows "a \<approx>\<^bsub>d\<^esub> b"
proof -
  have "?P \<le> gfp (euttF d)" 
  proof (intro coinduct[OF euttF_mono] predicate2I, elim exE conjE)
    fix x y a' b' assume a: "P a' b'" "x \<leadsto> a'" "y \<leadsto> b'"
    hence "euttF d (\<lambda>a b. ?P a b \<or> a \<approx>\<^bsub>d\<^esub> b) a' b'" using assms(2) by auto
    hence "euttF d (sup ?P (gfp (euttF d))) a' b'" 
      by (simp add: euttF_mono euttF_mono_helper eutt_peel gfp_fixpoint) 
    thus "euttF d (sup ?P (gfp (euttF d))) x y" using a(2,3) by blast
  qed
  thus ?thesis using assms(1) unfolding eutt_def by auto
qed

text \<open>Helper for the strong coinductive form\<close>
lemma euttF_disjI:
  assumes "a \<approx>\<^bsub>d\<^esub> b"
  shows "euttF d (\<lambda>a b. P a b \<or> a \<approx>\<^bsub>d\<^esub> b) a b"
  using assms
  by (metis (mono_tags, lifting) euttF_mono_helper eutt_def eutt_peel)

lemma eutt_sync_r[consumes 1, case_names ret io inf]:
  assumes "P a b"
  assumes "\<And>v a b. P a b \<Longrightarrow> b \<leadsto> Ret v \<Longrightarrow> \<exists>v'. a \<leadsto> Ret v' \<and> d v' v"
  assumes "\<And>e f b a. P a b \<Longrightarrow> b \<leadsto> IO e f \<Longrightarrow> \<exists>f'. a \<leadsto> IO e f' \<and> (\<forall>v. P (f' v) (f v) \<or> f' v \<approx>\<^bsub>d\<^esub> f v)"
  assumes "\<And>a b a' b'. P a b \<Longrightarrow> b = silent \<Longrightarrow> a = silent"
  shows "a \<approx>\<^bsub>d\<^esub> b"
proof -
  have "P \<le> euttF d (sup P (gfp (euttF d)))"
  proof
    fix x y assume p: "P x y"
    show "euttF d (sup P (gfp (euttF d))) x y"
    proof (cases y rule: next_event)
      case inf
      hence "x = silent" using assms(4) p by auto
      then show ?thesis using inf silent.code by (metis euttF_TauI p sup2CI)
    next
      case (ret r)
      then obtain r' where "x \<leadsto> Ret r'" "d r' r" using assms(2) p by blast
      then show ?thesis using ret by auto
    next
      case (io e f)
      then obtain f' where "x \<leadsto> IO e f'" "\<forall>v. P (f' v) (f v) \<or> f' v \<approx>\<^bsub>d\<^esub> f v" 
        using assms(3) p by blast
      then show ?thesis using io 
        by (simp add: euttF_IOI euttF_tausLI euttF_tausRI eutt_def)
    qed
  qed
  with euttF_mono have "P \<le> gfp (euttF d)" by (rule coinduct)
  thus ?thesis using assms(1) eutt_def by blast
qed

lemma eutt_sync[consumes 1, case_names sil ret io both left right]:
  assumes "P a b"
  assumes sil: "\<And>a b. P a b \<Longrightarrow> a = silent \<or> b = silent \<Longrightarrow> a = silent \<and> b = silent"
  assumes ret: "\<And>a b v. P a b \<Longrightarrow> a = Ret v \<Longrightarrow> \<not>is_Tau b \<Longrightarrow> 
                \<exists>v'. b = Ret v' \<and> d v v'"
  assumes io: "\<And>a b e f. P a b \<Longrightarrow> a = IO e f \<Longrightarrow> \<not>is_Tau b \<Longrightarrow> 
                (\<exists>f'. b = IO e f' \<and> (\<forall>v. P (f v) (f' v) \<or> f v \<approx>\<^bsub>d\<^esub> f' v))"

  assumes "\<And>b a b' a'. P a b \<Longrightarrow> b = Tau b' \<Longrightarrow> a = Tau a' \<Longrightarrow> 
                          \<exists>a'' b''. a' \<leadsto> a'' \<and> b' \<leadsto> b'' \<and> P a'' b''"
  assumes "\<And>b a b'. P a b \<Longrightarrow> b = Tau b' \<Longrightarrow> \<not> is_Tau a \<Longrightarrow> P a b'"
  assumes "\<And>b a a'. P a b \<Longrightarrow> a = Tau a' \<Longrightarrow> \<not> is_Tau b \<Longrightarrow> P a' b"

  shows "a \<approx>\<^bsub>d\<^esub> b"
  using assms
proof -
  have "P \<le> euttF d (sup P (gfp (euttF d)))"
  proof
    fix x y assume p: "P x y"
    show "euttF d (sup P (gfp (euttF d))) x y"
    proof (cases "x = silent")
      case True
      then show ?thesis using p sil by blast
    next
      case False
      then obtain x' where x: "x \<leadsto> x'" "\<not> is_Tau x'" using always_tau by auto 
      then show ?thesis
      proof (cases "y = silent")
        case True
        then show ?thesis using p sil by blast
      next
        case False
        then obtain y' where y: "y \<leadsto> y'" "\<not> is_Tau y'" using always_tau by auto 
        have "P x' y'" using x(1) y(1) 
        proof (induct rule: ftp_induct_dual_rev)
          case fin
          then show ?case using x(2) y(2) by auto
        next
          case base
          then show ?case using p by auto
        next
          case (left a)
          then show ?case using assms(7) y(2) by blast
        next
          case (right b)
          then show ?case using assms(6) x(2) by blast
        next
          case (both a b)
          then show ?case using assms(5) by blast
        qed
        hence "euttF d (sup P (gfp (euttF d))) x' y'" using ret io x(2) y(2)
          apply (cases x'; cases y'; auto)
             apply fastforce
            apply fastforce
           apply fastforce
          by (metis (full_types) euttF_IOI eutt_def sup2I1 sup2I2 y(2))
        thus ?thesis using x(1) y(1) by blast 
      qed
    qed
  qed
  with euttF_mono have "P \<le> gfp (euttF d)" by (rule coinduct)
  thus ?thesis using assms(1) eutt_def by blast
qed

(*
*)


subsection \<open>Transitive\<close>

definition mergep
  where "mergep f\<^sub>1 f\<^sub>2 \<equiv> \<lambda>a b. \<exists>c. f\<^sub>1 a c \<and> f\<^sub>2 c b"

lemma mergepI [intro]:
  assumes "f\<^sub>1 a b" "f\<^sub>2 b c"
  shows "mergep f\<^sub>1 f\<^sub>2 a c"
  using assms by (auto simp: mergep_def)

lemma mergepE [elim]:
  assumes "mergep f\<^sub>1 f\<^sub>2 a c"
  obtains b where "f\<^sub>1 a b" "f\<^sub>2 b c"
  using assms by (auto simp: mergep_def)

lemma euttF_TauLE2 [euttF_elims]:
  assumes "euttF d S (Tau l) b"
  obtains r where "b \<leadsto> Tau r" "S l r" | "euttF d S l b"
  using assms by (induct "Tau l :: ('a, 'c, 'd) itree" b) (blast)+

lemma eutt_trans:
  assumes "a \<approx>\<^bsub>r\<^sub>1\<^esub> b" "b \<approx>\<^bsub>r\<^sub>2\<^esub> c"
  shows "a \<approx>\<^bsub>mergep r\<^sub>1 r\<^sub>2\<^esub> c"
  using assms
proof (coinduction arbitrary: a b c rule: eutt_sync_r)
  case ret
  then show ?case 
    apply -
    apply (erule eutt_TausRE[of _ ba], blast)
    apply (auto elim!: eutt_elims)
    apply (erule eutt_TausRE[of _ aa], blast)
    apply (auto elim!: eutt_elims)
    done
next
  case io
  then show ?case 
    apply -
    apply (erule eutt_TausRE[of _ ba], blast)
    apply (auto elim!: eutt_elims)
    apply (erule eutt_TausRE[of _ aa], blast)
    apply (auto elim!: eutt_elims)
    by blast
next
  case inf
  then show ?case by auto
qed

lemma eutt_eq_trans [intro,trans]:
  assumes "x \<cong> z" "z \<cong> y" shows "x \<cong> y"
  using eutt_trans[OF assms] by (auto simp: mergep_def)

subsection \<open>Conseq\<close>

lemma euttF_conseqI:
  assumes "euttF r T a b" "r \<le> e"
  assumes "\<And>k1 k2. T k1 k2 \<Longrightarrow> S k1 k2"
  shows "euttF e S a b"
  using assms by (induct) auto

lemma eutt_conseqI:
  assumes "a \<approx>\<^bsub>r\<^esub> b" "r \<le> e"
  shows  "a \<approx>\<^bsub>e\<^esub> b"
  using assms(1)
proof (coinduction arbitrary: a b rule: eutt_fp)
  case fp
  hence "euttF r (\<approx>\<^bsub>r\<^esub>) aa ba" by (simp add: euttF_mono eutt_peel gfp_fixpoint)
  thus ?case using assms(2) by (rule euttF_conseqI) auto
qed

lemma eutt_rwI [intro]:
  assumes "a \<approx>\<^bsub>d\<^esub> b"
  assumes "a \<cong> a'" "b \<cong> b'"
  shows "a' \<approx>\<^bsub>d\<^esub> b'"
  using eutt_trans[OF eutt_trans[OF eutt_eq_sym[OF assms(2)] assms(1)] assms(3)]
  by (auto simp: mergep_def)

text \<open>
A specialised rewrite operation, where we establish @{term euttF} over two non-tau
itrees that are known to be equivalent to another pair.
Therefore, the @{term euttF} relation should transfer over to the other pair.
\<close>
lemma euttF_rw_nontauI:
  assumes "euttF d T a' b'"
  assumes "a \<cong> a'" "\<not> is_Tau a'"
  assumes "b \<cong> b'" "\<not> is_Tau b'"
  assumes "\<And>a a' b b'. T a' b' \<Longrightarrow> a \<cong> a' \<Longrightarrow> b \<cong> b' \<Longrightarrow> S a b"
  shows "euttF d S a b"
  using assms(2,1,3)
  unfolding eutt_peel
proof (induct)
  case (euttF_RetI a b)
  show ?case using assms(4,5) euttF_RetI(2)
    unfolding eutt_peel euttF_RetI(1) 
    by (induct) (auto elim: euttF.cases)
next
  case (euttF_IOI k1 k2 e)
  show ?case using assms(4,5) euttF_IOI(1,2)
    unfolding eutt_peel
  proof (induct)
    case (euttF_RetI a b)
    then show ?case by (auto elim: euttF.cases)
  next
    case (euttF_IOI k1' k2' e')
    then show ?case using assms(6)
      by (auto simp: eutt_def[symmetric] elim!: euttF.cases) blast
  qed auto
qed auto

subsection \<open>Bind\<close>

lemma euttF_bindI:
  assumes "euttF r S a b" 
  assumes "\<And>l l'. r l l' \<Longrightarrow> euttF e T (c l) (d l')"
  assumes "\<And>k1 k2. S k1 k2 \<Longrightarrow> T (k1 \<bind> c) (k2 \<bind> d)"
  shows "euttF e T (a \<bind> c) (b \<bind> d)"
  using assms by (induct) (auto simp: bind_simps)

text \<open>
Given we can relate the initial components of a bind, such that we can then
relate the corresponding subsequent components, the binds should be equivalent.
\<close>
lemma eutt_bindI [intro]:
  assumes "a \<approx>\<^bsub>\<lambda>l l'. c l \<approx>\<^bsub>e\<^esub> d l'\<^esub> b"
  shows "(a \<bind> c) \<approx>\<^bsub>e\<^esub> (b \<bind> d)"
  using assms
proof (coinduction arbitrary: a b rule: eutt_fp)
  case fp
  let ?r="\<lambda>l l'. c l \<approx>\<^bsub>e\<^esub> d l'"
  have "euttF ?r (gfp (euttF ?r)) aa ba" using fp by (auto simp: eutt_peel)
  then show ?case
  proof (rule euttF_bindI, goal_cases)
    case (1 l l')
    then show ?case using euttF_disjI by fast 
  next
    case (2 k1 k2)
    then show ?case unfolding eutt_def[symmetric] by auto
  qed
qed

text \<open>
A complex coinductive proof to enable the subsequent coinductive proof method.
\<close>
lemma prefix_fp:
  assumes "\<And>a b. F a b \<Longrightarrow> 
           (a \<approx>\<^bsub>d\<^esub> b) \<or>
           (\<exists>(pa :: ('a, 'b, 'c) itree) (pb :: ('d, 'b, 'c) itree) a' b'. 
              a \<cong> pa \<bind> a' \<and> b \<cong> pb \<bind> b' \<and> 
              pa \<approx>\<^bsub>\<lambda>v v'. (\<exists>a b. F a b \<and> a' v \<cong> a \<and> b' v' \<cong> b)\<^esub> pb \<and> (\<nexists>v. pa \<cong> Ret v))"
    (is "\<And>a b. F a b \<Longrightarrow> ?EQ a b \<or> 
                          (\<exists>pa pb a' b'. ?F a pa a' \<and> ?S b pb b' \<and> ?FP pa pb a' b' \<and> ?NR pa)")
  assumes fp: "?FP (pa :: ('a, 'b, 'c) itree) (pb :: ('d, 'b, 'c) itree) a' b'"
              "a \<cong> pa \<bind> a'" "b \<cong> pb \<bind> b'" 
  shows "a \<approx>\<^bsub>d\<^esub> b"
  using fp
proof (coinduction arbitrary: a b pa pb a' b' rule: eutt_fp)
  case fp
  then show ?case (is "?P aa ba")
  proof (cases "pa" rule: next_event)
    case inf
    then show ?thesis using fp by auto
  next
    case (ret v)
    hence pa: "pa \<cong> return v" by auto
    hence "?FP (return v) pb a' b'" using fp by auto
    then obtain v' a b where f: "pb \<cong> return v'" "F a b" "a' v \<cong> a" "b' v' \<cong> b"
      by (auto elim!: eutt_elims)

    have "pb \<bind> b' \<cong> return v' \<bind> b'"
      using f(1) by (rule eutt_bindI[OF eutt_conseqI]) auto
    hence b: "ba \<cong> return v' \<bind> b'" using fp by blast
    have "pa \<bind> a' \<cong> return v \<bind> a'"
      using pa by (rule eutt_bindI[OF eutt_conseqI]) auto
    hence a: "aa \<cong> return v \<bind> a'" using fp by blast

    then show ?thesis using assms(1)[OF f(2)]
    proof (elim disjE, goal_cases)
      case 1
      hence "a' v \<approx>\<^bsub>d\<^esub> b' v'" using f(3,4) by (auto)
      hence "aa \<approx>\<^bsub>d\<^esub> ba" using a b by (auto simp: bind_simps)
      then show ?case by (simp add: euttF_disjI)
    next
      case 2
      then obtain pa pb a' b' where e:
          "a \<cong> (pa :: ('a, 'b, 'c) itree) \<bind> a'" "b \<cong> (pb :: ('d, 'b, 'c) itree) \<bind> b'" 
          "pa \<approx>\<^bsub>\<lambda>v v'. \<exists>a b. F a b \<and> a' v \<cong> a \<and> b' v' \<cong> b\<^esub> pb" "(\<nexists>v. pa \<cong> return v)"
        by auto

      hence a': "aa \<cong> pa \<bind> a'" using a f(3) by (auto simp: bind_simps)
      hence b': "ba \<cong> pb \<bind> b'" using e b f(4) by (auto simp: bind_simps)

      then show ?case
      proof (cases "pa" rule: next_event)
        case inf
        then show ?thesis using a' b' e by (auto simp: bind_simps)
      next
        case (ret r)
        then show ?thesis using e by auto
      next
        case (io e f)
        hence pa: "pa \<cong> IO e f" by auto
        hence "?FP (IO e f) pb a' b'" using e io by auto
        then obtain f' where f: "pb \<cong> IO e f'" "\<forall>v. ?FP (f v) (f' v) a' b'"
          by (auto elim!: eutt_elims)
        hence p: "euttF d (\<lambda>a b. (\<exists>pa pb a'a b'a. pa \<approx>\<^bsub>\<lambda>v v'. \<exists>a b. F a b \<and> a'a v \<cong> a \<and> b'a v' \<cong> b\<^esub> pb \<and> a \<cong> (pa :: ('a, 'b, 'c) itree) \<bind> a'a \<and> b \<cong> (pb :: ('d, 'b, 'c) itree) \<bind> b'a)) (IO e f \<bind> a') (IO e f' \<bind> b')"
          by (auto simp add: bind_simps) blast

        have "pb \<bind> b' \<cong> IO e f' \<bind> b'"
          using f(1) by (rule eutt_bindI[OF eutt_conseqI]) auto
        hence b: "ba \<cong> IO e f' \<bind> b'" using b' by auto
        have "pa \<bind> a' \<cong> IO e f \<bind> a'"
          using pa by (rule eutt_bindI[OF eutt_conseqI]) auto
        hence a: "aa \<cong> IO e f \<bind> a'" using a' by auto

        show ?thesis 
          apply (rule euttF_rw_nontauI[OF p a _ b])
          by (auto simp: bind_simps) blast
      qed
    qed
  next
    case (io e f)
    hence pa: "pa \<cong> IO e f" by auto
    hence "?FP (IO e f) pb a' b'" using fp by auto
    then obtain f' where f: "pb \<cong> IO e f'" "\<And>v. ?FP (f v) (f' v) a' b'"
      by (auto elim!: eutt_elims)
    hence p: "euttF d (\<lambda>a b. (\<exists>pa pb a'a b'a. pa \<approx>\<^bsub>\<lambda>v v'. \<exists>a b. F a b \<and> a'a v \<cong> a \<and> b'a v' \<cong> b\<^esub> pb \<and> a \<cong> (pa :: ('a, 'b, 'c) itree) \<bind> a'a \<and> b \<cong> (pb :: ('d, 'b, 'c) itree) \<bind> b'a)) (IO e f \<bind> a') (IO e f' \<bind> b')"
      by (auto simp add: bind_simps) blast

    have "pb \<bind> b' \<cong> IO e f' \<bind> b'"
      using f(1) by (rule eutt_bindI[OF eutt_conseqI]) auto
    hence b: "ba \<cong> IO e f' \<bind> b'" using fp by blast
    have "pa \<bind> a' \<cong> IO e f \<bind> a'"
      using pa by (rule eutt_bindI[OF eutt_conseqI]) auto
    hence a: "aa \<cong> IO e f \<bind> a'" using fp by blast

    show ?thesis 
      apply (rule euttF_rw_nontauI[OF p a _ b])
      by (auto simp: bind_simps) blast
  qed
qed

text \<open>
A coinductive proof method that allows for two itrees to be shown to be bisimilar given some series
of non-trivial prefixes can be related, until the remaining components can be directly shown
to be equivalent.

The fixed point FP effectively encodes cut-points between the two itrees, denoting
points where it is possible to either directly compare the itrees or argue for their progress
to another cut-point.

Note that this notion of progress to another itree must either take the form of an observable
event or silent non-termination.
\<close>
lemma prefix_coinduct:
  assumes "F a b"
  assumes "\<And>a b. F a b \<Longrightarrow> 
           (a \<approx>\<^bsub>d\<^esub> b) \<or>
           (\<exists>pa pb a' b'. a \<cong> pa \<bind> a' \<and> b \<cong> pb \<bind> b' \<and>
              pa \<approx>\<^bsub>\<lambda>v v'. (\<exists>a b. F a b \<and> a' v \<cong> a \<and> b' v' \<cong> b)\<^esub> pb \<and> (\<nexists>v. pa \<cong> Ret v))"
  shows "a \<approx>\<^bsub>d\<^esub> b"
  using assms(2)[OF assms(1)]
proof (elim disjE exE conjE, goal_cases)
  case 1
  then show ?case by auto
next
  case (2 pa pb a' b')
  show ?case using assms(2) by (rule prefix_fp[OF _ 2(3,1,2)]) auto
qed

end