theory Silent
  imports ITrees
begin

section \<open>Silent Interaction Trees\<close>

text \<open>
We introduce the notion of an @{type itree} that performs infinite silent
internal steps. This structure eliminates a variety of operators trivially
and becomes useful in introducing a notion of an @{type itree}'s next
observable event, if one exists.
\<close>

primcorec silent
  where "silent = Tau silent"

subsection \<open>Deconstruction Properties\<close>

text \<open>
Applying the @{term Tau} constructor to @{term silent} should have no effect,
as the structure denotes the greatest fixed-point of @{term Tau} constructors.
This lemma must be carefully applied however, as it interferes with case analysis.\<close>
lemma silent_fp:
  "Tau silent = silent"
  using silent.code by metis

text \<open>
Trivially, @{term silent} is not equal to any observable @{type itree}.
We register such properties against the standard simplification theorem set.
\<close>
lemma silent_simps [simp]:
  "is_Ret silent = False"
  "is_IO silent = False"
  "is_Tau silent = True"
  by (subst silent.code, simp)+

lemma [simp]:
  "(silent = return r) = False"
  "(return r = silent) = False"
  by (metis silent.disc_iff itree.disc(4))+

lemma [simp]:
  "(silent = IO e f) = False"
  "(IO e f = silent) = False"
  by (metis silent.disc_iff itree.disc(6))+

lemma tau_silentE:
  assumes "Tau k = silent \<or> silent = Tau k"
  shows "k = silent"
  using assms
proof (coinduction arbitrary: k)
  case ret
  then show ?case by (clarsimp, elim disjE) (subst (asm) silent.code, auto)+
next
  case tau
  then show ?case using silent.code by (metis itree.sel(2))
next
  case io
  then show ?case by (clarsimp, elim disjE) (subst (asm) silent.code, auto)+
qed

lemma [simp]:
  "(Tau k = silent) = (k = silent)"
  "(silent = Tau k) = (k = silent)"
  using tau_silentE by (auto simp: silent_fp) 

subsection \<open>@{term silent} Properties\<close>

text \<open>
The application of operators to @{term silent} will generally produce
a @{term silent} result.
\<close>

lemma bind_silent [simp]:
  "silent \<bind> f = silent"
proof (coinduction)
  case tau
  hence "silent \<bind> f = (Tau silent) \<bind> f" by (auto simp: silent_fp) 
  also have "... = Tau (silent \<bind> f)" unfolding itree_simps by blast
  finally show ?case using tau by (auto elim!: itree_elims)
qed (auto elim!: itree_elims)

lemma fmap_silent [simp]:
  "silent \<oplus> f = silent"
  by (auto simp: itree_fmap_def)

lemma emap_silent [simp]:
  "silent \<oplus>\<guillemotleft>ot,it\<guillemotright> = silent"
proof (coinduction)
  case tau
  hence "silent \<oplus>\<guillemotleft>ot,it\<guillemotright> = (Tau silent) \<oplus>\<guillemotleft>ot,it\<guillemotright>" by (auto simp: silent_fp) 
  also have "... = Tau (silent \<oplus>\<guillemotleft>ot,it\<guillemotright>)" unfolding itree_simps by blast
  finally show ?case using tau by (auto elim!: itree_elims)
qed (auto elim!: itree_elims)

section \<open>Finite Tau Prefix\<close>

text \<open>
Throughout the proofs, it is often useful to consider @{type itree}s after some finite number of
@{term Tau}s have been stripped off. We introduce an inductive relation to encode such a prefix.
\<close>

inductive ftp :: "('a, 'b, 'c) itree \<Rightarrow> ('a, 'b, 'c) itree \<Rightarrow> bool"
  (infix "\<leadsto>" 53)
  where
    ftp_refl[intro]: "ftp t t" |
    ftp_tauI[intro]: "ftp t' t \<Longrightarrow> ftp (Tau t') t" 

subsection \<open>Induction Rule\<close>

text \<open>We redefine the induction rule for @{term ftp} to fix the based @{type itree} as constant.\<close>

lemma ftp_induct [induct pred: ftp]:
  assumes "a \<leadsto> b"
  assumes "P b"
  assumes "\<And>t. t \<leadsto> b \<Longrightarrow> P t \<Longrightarrow> P (Tau t)"
  shows "P a"
  using assms
proof (induct)
  case (ftp_refl t)
  then show ?case by auto
next
  case (ftp_tauI t' t)
  then show ?case by fast
qed

subsection \<open>Deconstruction Properties\<close>

lemma ftp_ret [simp]:
  "(return v \<leadsto> m) = (m = return v)"
  by (auto elim!: ftp.cases)

lemma ftp_io [simp]:
  "(IO e f \<leadsto> m) = (m = IO e f)"
  by (auto elim!: ftp.cases)

lemma ftp_silent [simp]:
  "(silent \<leadsto> m) = (m = silent)"
proof
  assume "silent \<leadsto> m"
  thus "m = silent" by (induct "silent :: ('a, 'b, 'c) itree" m) auto
qed auto

lemma [simp]:
  assumes "a \<leadsto> silent" 
  shows "a = silent"
  using assms by (induct; auto)

subsection \<open>@{term ftp} Properties\<close>

lemma ftp_tau_both [intro]:
  assumes "a \<leadsto> b"
  shows "Tau a \<leadsto> Tau b"
  using assms by induct auto

text \<open>
@{term ftp} features a number of standard properties, as it is effectively the reflexive-transitive
closure of the @{term Tau} constructor.
We demonstrate notions of transitivity and congruence.
\<close>

lemma ftp_trans [trans]:
  assumes "a \<leadsto> b" "b \<leadsto> c"
  shows "a \<leadsto> c"
  using assms by (induct) auto

lemma ftp_cong:
  assumes "a \<leadsto> b" "a \<leadsto> c"
  shows "b \<leadsto> c \<or> c \<leadsto> b"
  using assms
proof (induct arbitrary: c)
  case (1)
  then show ?case by blast
next
  case (2 tt)
  show ?case using 2(3,1,2) by (cases rule: ftp.cases[case_names a b]) blast+
qed

text \<open>
Additionally, a finite prefix is maintained across the set of existing operators.
\<close>

lemma bind_ftp [intro]:
  assumes "a \<leadsto> b"
  shows "(a \<bind> f) \<leadsto> (b \<bind> f)"
  using assms by (induct) (auto simp: bind_simps)

lemma fmap_ftp [intro]:
  assumes "a \<leadsto> b"
  shows "(a \<oplus> f) \<leadsto> (b \<oplus> f)"
  using assms by (induct) (auto simp: itree_simps)

lemma emap_ftp [intro]:
  assumes "a \<leadsto> b"
  shows "(a \<oplus>\<guillemotleft>ot,it\<guillemotright>) \<leadsto> (b \<oplus>\<guillemotleft>ot,it\<guillemotright>)"
  using assms by (induct) (auto simp: itree_simps)

section \<open>Next Event\<close>

text \<open>
Given notions of @{term silent} and @{term ftp} we introduce a new case analysis over
@{type itree}s, breaking into:
  \<^item> A @{term silent} structure
  \<^item> A finite number of @{term Tau}s followed by a @{term return}
  \<^item> A finite number of @{term Tau}s followed by a @{term IO}

This is obviously the case, as the structure is either @{term Tau} forever,
or there is some prefix to a non-@{term Tau} constructor.
\<close>

lemma always_tau:
  assumes "\<forall>v. m \<leadsto> v \<longrightarrow> is_Tau v" 
  shows "m = silent"
  using assms by (coinduction arbitrary: m) auto

lemma next_event:
  obtains (inf) "m = silent" | (ret) r where "m \<leadsto> return r" | (io) e f where "m \<leadsto> IO e f"
proof (cases "\<forall>v. m \<leadsto> v \<longrightarrow> is_Tau v")
  case True
  then show ?thesis using always_tau inf by auto
next
  case False
  then obtain v where "m \<leadsto> v" "\<not> is_Tau v" by auto
  then show ?thesis using ret io by (cases v) auto
qed

section \<open>@{term ftp} with Size\<close>

text \<open>A series of inductive lemmas to assist in coinductive proofs by deconstructing @{term Tau}
prefixes down to some event.\<close>

inductive ftp_size
  where 
    "ftp_size 0 a a" |
    "ftp_size n a b \<Longrightarrow> ftp_size (Suc n) (Tau a) b"

lemma ftp_size_both:
  assumes "ftp_size n a b"
  shows "ftp_size n (Tau a) (Tau b)"
  using assms by (induct) (auto intro: ftp_size.intros)

lemma ftp_size_split:
  assumes "ftp_size n a a'" "n > m"
  obtains x where "ftp_size m a x" "ftp_size (n - m) x a'"
  using assms
proof (induct)
  case (1 a)
  then show ?case by auto
next
  case (2 n a b)
  then show ?case
    apply (cases "m = n"; auto intro: ftp_size_both ftp_size.intros)
    by (metis Suc_diff_le ftp_size.intros(2) ftp_size_both less_Suc_eq_le)
qed

lemma ftp_with_size:
  assumes "a \<leadsto> a'"
  obtains n where "ftp_size n a a'"
  using assms by (induct) (auto intro: ftp_size.intros)

lemma ftp_size_dual [consumes 2]:
  assumes "ftp_size n a a'" "ftp_size n b b'"
  assumes "P a' b'"
  assumes "\<And>a b. P a b \<Longrightarrow> P (Tau a) (Tau b)"
  shows "P a b"
  using assms
  by (induct arbitrary: b) (auto elim: ftp_size.cases)

lemma ftp_size_sync:
  assumes "ftp_size n a a'" "ftp_size m b b'"
  assumes "P a' b'"
  assumes "\<And>a. P a b' \<Longrightarrow> P (Tau a) b'"
  assumes "\<And>b. P a' b \<Longrightarrow> P a' (Tau b)"
  assumes "\<And>a b. P a b \<Longrightarrow> P (Tau a) (Tau b)"
  shows "P a b"
  using assms
proof -
  consider "n = m" | "n > m" | "n < m" by force
  thus ?thesis
  proof (cases)
    case 1
    show ?thesis using assms(1,2,3,6) unfolding 1 by (induct rule: ftp_size_dual) auto
  next
    case 2
    then obtain x where x: "ftp_size m a x" "ftp_size (n - m) x a'"
    using ftp_size_split assms(1) by blast
    have "P x b'" using x(2) assms(3,4) by (induct) auto
    with x(1) assms(2) show ?thesis using assms(6) by (induct rule: ftp_size_dual) auto
  next
    case 3
    then obtain x where x: "ftp_size n b x" "ftp_size (m - n) x b'"
      using ftp_size_split assms(2) by blast
    have "P a' x" using x(2) assms(3,5) by (induct) auto
    with assms(1) x(1) show ?thesis using assms(6) by (induct rule: ftp_size_dual) auto
  qed
qed

lemma ftp_size_sync':
  assumes "ftp_size n a a'" "ftp_size m b b'"
  assumes "P a b"
  assumes "\<And>a. P (Tau a) b' \<Longrightarrow> P a b'"
  assumes "\<And>b. P a' (Tau b) \<Longrightarrow> P a' b"
  assumes "\<And>a b. P (Tau a) (Tau b) \<Longrightarrow> P a b"
  shows "P a' b'"
  using assms
proof -
  consider "n = m" | "n > m" | "n < m" by force
  thus ?thesis
  proof (cases)
    case 1
    show ?thesis using assms(1,2,3,6) unfolding 1 by (induct rule: ftp_size_dual) auto
  next
    case 2
    then obtain x where x: "ftp_size m a x" "ftp_size (n - m) x a'"
      using ftp_size_split assms(1) by blast
    have "P x b'" using x(1) assms(2,3,6) by (induct rule: ftp_size_dual) auto
    with x(2) show ?thesis using assms(4) by (induct) auto
  next
    case 3
    then obtain x where x: "ftp_size n b x" "ftp_size (m - n) x b'"
      using ftp_size_split assms(2) by blast
    have "P a' x" using x(1) assms(1,3,6) by (induct rule: ftp_size_dual) auto
    with x(2) show ?thesis using assms(5) by (induct) auto
  qed
qed

lemma progress_fp:
  assumes "ftp_size n a ma" "ftp_size m b mb" 
  assumes "ma \<leadsto> a'" "mb \<leadsto> b'" "\<not> is_Tau a'" "\<not> is_Tau b'"
  assumes base: "P a b"
  assumes left: "\<And>a. P (Tau a) b' \<Longrightarrow> \<exists>a'. a \<leadsto> a' \<and> P a' b'"
  assumes right: "\<And>b. P a' (Tau b) \<Longrightarrow> \<exists>b'. b \<leadsto> b' \<and> P a' b'"
  assumes both: "\<And>a b. P (Tau a) (Tau b) \<Longrightarrow> \<exists>a' b'. a \<leadsto> a' \<and> b \<leadsto> b' \<and> P a' b'"
  shows "\<exists>ma' mb'. ma \<leadsto> ma' \<and> mb \<leadsto> mb' \<and> P ma' mb'"
  using assms(1,2,3,4,5,6)
proof (induct rule: ftp_size_sync'[consumes 2])
  case 1
  then show ?case using base by auto
next
  case (2 a)
  then obtain ma' mb' where p: "Tau a \<leadsto> ma'" "mb \<leadsto> mb'" "P ma' mb'"
    by blast
  hence "\<not>is_Tau mb' \<Longrightarrow> mb' = b'"
    using 2 by (metis ftp.cases ftp_cong itree.disc(5))
  moreover have "is_Tau mb' \<Longrightarrow> \<exists>mb''. mb' = Tau mb''"
    by (cases mb'; auto)
  ultimately show ?case using p left
    apply (auto elim!: ftp.cases[of "Tau a"])
    apply (cases "is_Tau mb'"; auto)
    apply (drule both; auto)
    by (meson ftp_tauI ftp_trans)
next
  case (3 b)
  then obtain ma' mb' where p: "ma \<leadsto> ma'" "Tau b \<leadsto> mb'" "P ma' mb'"
    by blast
  hence "\<not>is_Tau ma' \<Longrightarrow> ma' = a'"
    using 3 by (metis ftp.cases ftp_cong itree.disc(5))
  moreover have "is_Tau ma' \<Longrightarrow> \<exists>ma''. ma' = Tau ma''"
    by (cases ma'; auto)
  ultimately show ?case using p right
    apply (auto elim!: ftp.cases[of "Tau b"])
    apply (cases "is_Tau ma'"; auto)
    apply (drule both; auto)
    by (meson ftp_tauI ftp_trans)
next
  case (4 a b)
  then obtain ma' mb' where p: "Tau a \<leadsto> ma'" "Tau b \<leadsto> mb'" "P ma' mb'"
    by blast

  have "\<not>is_Tau ma' \<Longrightarrow> ma' = a'"
    using 4 p by (metis ftp.cases ftp_cong ftp_tauI itree.disc(5))
  moreover have "\<not>is_Tau mb' \<Longrightarrow> mb' = b'"
    using 4 p by (metis ftp.cases ftp_cong ftp_tauI itree.disc(5))
  moreover have "is_Tau ma' \<Longrightarrow> \<exists>ma''. ma' = Tau ma''"
    by (cases ma'; auto)
  moreover have "is_Tau mb' \<Longrightarrow> \<exists>mb''. mb' = Tau mb''"
    by (cases mb'; auto)

  ultimately show ?case using both p
    apply (auto elim!: ftp.cases[of "Tau b"] ftp.cases[of "Tau a"])
    apply (cases "is_Tau ma'"; cases "is_Tau mb'"; auto)
    apply (drule both; auto)
    apply (meson ftp_tauI ftp_trans)
    using left apply blast
    apply (cases "is_Tau ma'"; cases "is_Tau mb'"; auto)
    apply (drule both; auto)
    apply (meson ftp_tauI ftp_trans)
    using right apply blast
    done
qed

text \<open>
Given @{term a} and @{term b} reduce down to events @{term a'} and @{term b'}
respectively, and we know the inductive hypothesis @{term P} holds for 
@{term a} and @{term b}, deconstruction these @{type itree}s first
simultaneously and then progress through the @{term Tau} constructors that
remain on either the left or right sides.
\<close>
lemma ftp_induct_dual_rev[consumes 2, case_names fin base left right both]:
  assumes "a \<leadsto> a'" "b \<leadsto> b'"
  assumes "\<not>is_Tau a' \<and> \<not> is_Tau b'"
  assumes "P a b"
  assumes "\<And>a. P (Tau a) b' \<Longrightarrow> \<exists>a'. a \<leadsto> a' \<and> P a' b'"
  assumes "\<And>b. P a' (Tau b) \<Longrightarrow> \<exists>b'. b \<leadsto> b' \<and> P a' b'"
  assumes "\<And>a b. P (Tau a) (Tau b) \<Longrightarrow> \<exists>a' b'. a \<leadsto> a' \<and> b \<leadsto> b' \<and> P a' b'"
  shows "P a' b'"
  using assms
proof -
  obtain n m where "ftp_size n a a'" "ftp_size m b b'" 
                    "a' \<leadsto> a'" "b' \<leadsto> b'" "\<not> is_Tau a'" "\<not> is_Tau b'"
    using assms by (elim ftp_with_size) blast
  hence "\<exists>ma' mb'. a' \<leadsto> ma' \<and> b' \<leadsto> mb' \<and> P ma' mb'"
    using assms(4,5,6,7) by (rule progress_fp; blast)
  thus ?thesis using assms(3)  by (metis ftp.cases itree.disc(5))
qed

end