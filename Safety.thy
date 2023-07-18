theory Safety
  imports Silent Iteration Bisim
begin

section \<open>Verification\<close>

text \<open>
We encode a simple Hoare logic over @{type itree}s, such that we can establish an upper-bound
on the possible results and emitted events from a particular @{type itree} given an assumption
on the environment's responses to these emitted events.
\<close>

coinductive safe
  for res :: "'r \<Rightarrow> bool"
  and out :: "'o \<Rightarrow> bool"
  and io :: "'o \<Rightarrow> 'i \<Rightarrow> bool"
  where
    "res i \<Longrightarrow> safe res out io (Ret i)" |
    "safe res out io k \<Longrightarrow> safe res out io (Tau k)" |
    "\<forall>v. io e v \<longrightarrow> safe res out io (f v) \<Longrightarrow> out e \<Longrightarrow> safe res out io (IO e f)"

subsection \<open>Deconstruction Properties\<close>

text \<open>
Notably, we do not include any termination requirement, as @{term safe} simply encodes
a concept of safety. Consequently, @{term silent} is trivially safe.
Moreover, @{term safe} is preserved across finite @{term Tau} constructors.
\<close>

lemma safe_simps [itree_simps]:
  "safe res out io (return v) = res v"
  "safe res out io (Tau k) = safe res out io k"
  "safe res out io (IO e c) = (out e \<and> (\<forall>v. io e v \<longrightarrow> safe res out io (c v)))"
  by (auto intro: safe.intros elim: safe.cases)

lemma safe_silent [itree_simps]:
  "safe res out io silent"
  by (coinduction) auto

lemma safe_ftp:
  assumes "a \<leadsto> b"
  shows "safe res out io a = safe res out io b"
  using assms by (induct) (auto simp: safe_simps)

lemma safe_ftpI[intro]:
  assumes "a \<leadsto> b"
  assumes "safe res out io a" 
  shows "safe res out io b"
  using assms by (induct) (auto simp: safe_simps)

lemma safe_eutt:
  assumes "safe f g h a"
  assumes "a \<cong> b"
  shows "safe f g h b"
  using assms
proof (coinduction arbitrary: a b)
  case safe
  then show ?case
  proof (cases b)
    case (Ret r)
    hence "f r" using safe by (auto elim!: eutt_elims dest!: safe_ftp simp: safe_simps)
    then show ?thesis using Ret by simp
  next
    case (Tau k)
    hence "a \<cong> k \<and> safe f g h a"  using safe by (auto elim!: eutt_elims)
    then show ?thesis using Tau by blast
  next
    case (IO e k)
    then obtain f' where "a \<leadsto> IO e f'" "\<forall>v. (f' v) \<cong> (k v)" using safe by (auto elim!: eutt_elims)
    then show ?thesis using IO by (metis safe(1) safe_simps(3) safe_ftp)
  qed
qed

lemma safe_eutt_r:
  assumes "a \<approx>\<^bsub>Q\<^esub> b"
  assumes "safe f g h a"
  shows "safe (\<lambda>a. \<exists>b. f b \<and> Q b a) g h b"
  using assms
proof (coinduction arbitrary: a b)
  case safe
  then show ?case
  proof (cases b)
    case (Ret r)
    hence "\<exists>v. Q v r \<and> f v" 
      using safe by (auto elim!: eutt_elims dest!: safe_ftp[of a _ f g h] simp: safe_simps)
    then show ?thesis using Ret by auto
  next
    case (Tau k)
    hence "a \<approx>\<^bsub>Q\<^esub> k \<and> safe f g h a" using safe by (auto elim!: eutt_elims)
    then show ?thesis using Tau by blast
  next
    case (IO e k)
    then obtain f' where "a \<leadsto> IO e f'" "\<forall>v. (f' v) \<approx>\<^bsub>Q\<^esub> (k v)" 
      using safe by (auto elim!: eutt_elims)
    then show ?thesis using IO by (metis (no_types, lifting) safe(2) safe_simps(3) safe_ftp)
  qed
qed

subsection \<open>Consequence\<close>

text \<open>
A safety condition without any requirements on the result or emitted events is trivially true.
Moreover, it is possible to rewrite an existing safety property by weakening requirements
on the @{type itree} and strengthening requirements on the environment.
\<close>

lemma safe_trivial [itree_simps]:
  "safe (\<lambda>_. True) (\<lambda>_. True) io m"
proof (coinduction arbitrary: m)
  case safe
  then show ?case by (cases m; auto)
qed

lemma safe_conseq:
  assumes "safe res out io a"
  assumes "res \<le> res'"
  assumes "out \<le> out'"
  assumes "\<forall>e. out e \<longrightarrow> io' e \<le> io e"
  shows "safe res' out' io' a"
  using assms
proof (coinduction arbitrary: a)
  case safe
  then show ?case by (cases a) (auto simp: safe_simps)
qed

subsection \<open>Bind\<close>

text \<open>
Establishing safety over a @{term itree_bind} corresponds to establishing a safety property over
the first @{type itree} such that its results exhibit the desired safety property over
the second @{type itree}.
\<close>

lemma safe_bind:
  "safe res out io (a \<bind> b) = safe (\<lambda>v. safe res out io (b v)) out io a"
proof 
  assume "safe res out io (a \<bind> b)"
  thus "safe (\<lambda>v. safe res out io (b v)) out io a"
  proof (coinduction arbitrary: a)
    case safe
    then show ?case by (cases a) (auto simp: itree_simps)
  qed
next
  assume "safe (\<lambda>v. safe res out io (b v)) out io a"
  thus "safe res out io (a \<bind> b)"
  proof (coinduction arbitrary: a)
    case safe
    then show ?case
    proof (cases a)
      case (Ret r)
      thus ?thesis using safe by (cases "b r"; auto simp: itree_simps)
    next
      case (Tau x2)
      thus ?thesis using safe by (auto simp: itree_simps)
    next
      case (IO x31 x32)
      thus ?thesis using safe by (auto simp: itree_simps)
    qed
  qed
qed

text \<open>
Additionally, we can shift @{type itree} transforms, such as mapping operations, into
the specification.
\<close>

lemma safe_fmap:
  "safe res out io (m \<oplus> f) = safe (res o f) out io m"
  unfolding itree_fmap_def by (auto simp: safe_bind itree_simps comp_def)

lemma safe_emap:
  "safe res out io (m \<oplus>\<guillemotleft>ot,it\<guillemotright>) = safe res (out o ot) (\<lambda>e i. \<exists>i'. io (ot e) i' \<and> i = it i') m"
    (is "?L = ?R")
proof 
  assume ?L
  thus ?R
  proof (coinduction arbitrary: m)
    case safe
    then show ?case by (cases m) (auto simp: itree_simps)
  qed
next
  assume ?R
  thus ?L
    proof (coinduction arbitrary: m)
    case safe
    then show ?case by (cases m) (auto simp: itree_simps)
  qed
qed

subsection \<open>Iteration\<close>

text \<open>
Establishing safety over a @{term iter} or @{term loop} can be attained through the establishment
of a loop invariant, referred to as @{term I} in the following. The invariant must
preserve itself over loop bodies that will continue to iterate, and establish a desired final
 predicate (@{term E}) otherwise.
\<close>

lemma safe_iter:
  assumes "\<And>i. I i \<Longrightarrow> safe (I+\<^sub>fE) out op (f i)"
  assumes "safe (I+\<^sub>fE) out op a"
  shows "safe E out op (iter a f)"
  using assms(2)
proof (coinduction arbitrary: a)
  case safe
  then show ?case by (cases a rule: itree_sum_cases) (auto simp: itree_simps dest: assms(1))
qed

lemma safe_loop [consumes 1, case_names inv]:
  assumes "I i"
  assumes "\<And>i. I i \<Longrightarrow> safe (I+\<^sub>fE) out op (f i)"
  shows "safe E out op (loop f i)"
  using assms(2) assms(2)[OF assms(1)] unfolding loop_def
  by (rule safe_iter) auto

subsection \<open>Coinductive Lemmas\<close>

text \<open>
We can construct a stronger coinductive lemma for @{term safe} by considering the cases of it's
next event, rather than immediate @{type itree} constructors.
To achieve this, we must introduce a least fixed point variant of @{term safe} to encode
a finite number of steps between points at which a coinductive hypothesis (@{term P}) holds. 
\<close>

inductive safe\<^sub>l
  for res and out and io
  where
    "res a \<Longrightarrow> safe\<^sub>l res out io a" |
    "safe\<^sub>l res out io a \<Longrightarrow> safe\<^sub>l res out io (Tau a)" |
    "\<forall>v. io e v \<longrightarrow> safe\<^sub>l res out io (f v) \<Longrightarrow> out e \<Longrightarrow> safe\<^sub>l res out io (IO e f)"

text \<open>
Our coinductive hypothesis states that after a finite number of safe steps (those constraints
by the predicates @{term res}, @{term out}, @{term io}) we will arrive at an @{type itree} that
satisfies the underlying coinductive hypothesis (@{term P}) or is just directly known to be
@{term safe}.
Given this structure, we can consider the cases of a divergent @{type itree} and the 
constraints on its next event.
\<close>

lemma safe_event_coinduct_safe\<^sub>l:
  assumes "safe\<^sub>l (\<lambda>v. P v \<or> safe res out io v) out io a"
  assumes "\<And>a. P a \<Longrightarrow> (a = silent) \<or> 
                        (\<exists>v. a \<leadsto> return v \<and> res v) \<or>
                        (\<exists>e f. a \<leadsto> IO e f \<and> out e \<and> (\<forall>v. io e v \<longrightarrow> safe\<^sub>l (\<lambda>v. P v \<or> safe res out io v) out io (f v)))"
  shows "safe res out io a"
  using assms(1)
proof (coinduction arbitrary: a)
  case safe
  thus ?case
  proof (induct)
    case (1 a)
    then show ?case 
    proof (elim disjE, goal_cases)
      case 1
      then show ?case using assms(2)[OF 1]
      proof (elim disjE, goal_cases)
        case 1
        hence "a = Tau silent" "safe res out io silent" by (auto simp: silent_fp itree_simps)
        then show ?case by auto
      next
        case 2
        then show ?case by (metis (no_types, lifting) ftp.cases safe_ftp safe_simps(1))
      next
        case 3
        then obtain e f where i: "a \<leadsto> IO e f" "out e" 
            "\<forall>v. io e v \<longrightarrow> safe\<^sub>l (\<lambda>v. P v \<or> safe res out io v) out io (f v)" 
          by blast
        show ?case using i(1)
        proof (induct)
          case 1
          thus ?case using i by simp
        next
          case (2 t)
          thus ?case by (auto simp: itree_simps intro: safe\<^sub>l.intros(1,2) intro!: safe\<^sub>l.intros(3))
        qed
      qed
    next
      case 2
      then show ?case by (metis (mono_tags, opaque_lifting) safe.simps)
    qed
  next
    case (2 a)
    then show ?case by simp
  next
    case (3 f e)
    then show ?case by simp
  qed
qed

text \<open>
Given this result, we can attain a coinductive lemma that does not refer to @{term safe\<^sub>l} by
strengthening the assumptions.
\<close>

lemma safe_event_coinduct:
  assumes "P a"
  assumes "\<And>a. P a \<Longrightarrow> (a = silent) \<or> 
                        (\<exists>v. a \<leadsto> return v \<and> res v) \<or>
                        (\<exists>e f. a \<leadsto> IO e f \<and> out e \<and> (\<forall>v. io e v \<longrightarrow> P (f v) \<or> safe res out io (f v)))"
  shows "safe res out io a"
proof (rule safe_event_coinduct_safe\<^sub>l)
  show "safe\<^sub>l (\<lambda>v. P v \<or> safe res out io v) out io a" using assms(1) by (auto intro: safe\<^sub>l.intros)
next
  fix a assume "P a"
  thus "a = silent \<or>
         (\<exists>v. a \<leadsto> return v \<and> res v) \<or>
         (\<exists>e f. a \<leadsto> IO e f \<and>
                out e \<and> (\<forall>v. io e v \<longrightarrow> safe\<^sub>l (\<lambda>v. P v \<or> safe res out io v) out io (f v)))"
    using safe\<^sub>l.intros(1) assms(2) by (metis (no_types, lifting))
qed

end