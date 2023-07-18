theory Iteration
  imports Sum Bisim
begin

section \<open>Iteration\<close>

text \<open>
The iteration operator consumes an @{type itree} that returns a @{type sum}, with
a left result indicating progress on to the next iteration and a right result indicating
termination. To progress, a function denotes the next @{type itree} for a given
progress result.

To make the application of this more concrete, consider the first argument to @{term iter}
to be a basic block in a control flow graph that is part way through evaluation and will
return either the next block label to evaluate or the function's result.
\<close>
primcorec iter :: "('a+'b,'i,'o) itree \<Rightarrow> ('a \<Rightarrow> ('a+'b,'i,'o) itree) \<Rightarrow> ('b,'i,'o) itree"
  where "iter m f = (case m of exit v \<Rightarrow> Ret v
                             | prog v \<Rightarrow> Tau (iter (f v) f)
                             | Tau t \<Rightarrow> Tau (iter t f)
                             | IO e g \<Rightarrow> IO e (\<lambda>i. iter (g i) f))"

subsection \<open>Deconstruction Properties\<close>

lemma iter_simps [itree_simps]:
  "iter (return v) m = (case v of Inr v \<Rightarrow> Ret v | Inl l \<Rightarrow> Tau (iter (m l) m))"
  "iter (Tau k) m = Tau (iter k m)"
  "iter (IO e f) m = IO e (\<lambda>i. iter (f i) m)"
  by (simp add: iter.code)+

lemma iter_RetE [itree_elims]:
  assumes "iter m f = Ret v"
  obtains "m = exit v"
  using assms by (cases m rule: itree_sum_cases; auto simp: itree_simps)
  
lemma iter_TauE [itree_elims]:
  assumes "iter m f = Tau t"
  obtains (nxt) v where "m = prog v" "t = iter (f v) f" |
          (tau) k where "m = Tau k" "t = iter k f"
  using assms by (cases m rule: itree_sum_cases; auto simp: itree_simps)

lemma iter_IOE [itree_elims]:
  assumes "iter m f = IO e g"
  obtains h where "m = IO e h" "g = (\<lambda>i. iter (h i) f)"
  using assms by (cases m rule: itree_sum_cases; auto simp: itree_simps)

subsection \<open>@{term iter} Properties\<close>

text \<open>Map operations distribute into iteration, with similar effects as @{term itree_bind}.\<close>

lemma iter_fmap:
  "iter a m \<oplus> f = iter (a \<oplus> (map_sum id f)) (\<lambda>v. m v \<oplus> (map_sum id f))"
  by (coinduction arbitrary: a) (auto elim!: itree_elims simp: itree_simps)

lemma iter_emap:
  "iter a m \<oplus>\<guillemotleft>ot,it\<guillemotright> = iter (a \<oplus>\<guillemotleft>ot,it\<guillemotright>) (\<lambda>v. m v \<oplus>\<guillemotleft>ot,it\<guillemotright>)"
  by (coinduction arbitrary: a) (auto elim!: itree_elims simp: itree_simps)

text \<open>
We can unroll an @{term iter} by stripping off its current focus and binding it with
the composition of continued iteration or @{term return}.
Note that the @{term Tau} constructor is required in the progress case for full equivalence,
but not for @{term eutt}.
\<close>
lemma iter_unroll:
  "iter m f = (m \<bind> (\<lambda>v. Tau (iter (f v) f)) +\<^sub>f return)"
proof (coinduction arbitrary: m f)
  case ret
  then show ?case by (auto elim!: itree_elims simp: itree_simps)
next
  case tau
  then show ?case by (auto elim!: itree_elims simp: itree_simps) blast    
next
  case io
  then show ?case by (auto elim!: itree_elims simp: itree_simps) blast    
qed

lemma iter_unroll_eutt:
  "iter m f \<cong> (m \<bind> (\<lambda>v. iter (f v) f) +\<^sub>f return)"
  by (subst iter_unroll, intro eutt_refl eutt_bindI) (auto split: sum.splits)

text \<open>A iteration focus that will immediately exit can strip off the iteration entirely.\<close>
lemma iter_exit [simp]:
  "iter (x \<bind> exit) f = x"
  by (subst iter_unroll) (auto simp: itree_simps)

lemma iter_cong_unrollL:
  assumes "a \<bind> (Tau o f) +\<^sub>f exit = b"
  shows "iter a f = iter b f"
proof -
  have "iter a f = a \<bind> (\<lambda>v. Tau (iter (f v) f)) +\<^sub>f Ret" (is "_ = a \<bind> ?l")
    using iter_unroll by auto
  also have "... = a \<bind> (\<lambda>v. (Tau o f) v \<bind> ?l) +\<^sub>f Ret"
    by (subst iter_unroll) (auto simp: comp_def bind_simps)
  also have "... = a \<bind> (Tau o f) +\<^sub>f exit \<bind> ?l"
    using case_sum_bind[symmetric, of a "Tau o f" ?l exit]
    by (simp add: bind_simps)
  also have "... = b \<bind> ?l" using assms by blast
  also have "... = iter b f" using iter_unroll by metis
  finally show ?thesis .
qed

text \<open>It is possible to distribute a bind over an iteration, making it conditional on exit.\<close>
lemma bind_iter:
  "bind (iter m g) b = iter (bind m (bimap return b)) (\<lambda>v. bind (g v) (bimap return b))"
proof (coinduction arbitrary: m g b rule: itree.coinduct_strong)
  case Eq_itree
  then show ?case
    apply (cases "iter m g \<bind> b") 
      apply (auto simp: iter_simps bind_simps  split: sum.splits elim!: itree_elims)
      apply blast+
    done
qed

text \<open>
Given the interleaved iteration of two bodies, @{term f} and @{term g}, we can
peel off an iteration of the first, reversing their ordering in the iteration definition.
\<close>
lemma iter_rev:
  "iter a (\<lambda>i. f i \<bind> (Tau o g) +\<^sub>f exit) =
   iter (a \<bind> (Tau o f) +\<^sub>f exit) (\<lambda>i. g i \<bind> (Tau o f) +\<^sub>f exit)"
proof (coinduction arbitrary: a f g rule: itree_coinduct)
  case ret
  then show ?case by (auto elim!: itree_elims simp: bind_simps iter_simps)
next
  case tau
  then show ?case
  proof ((elim itree_elims;simp add: bind_simps iter_simps), goal_cases)
    case (1 v)
    have "iter (f v) (\<lambda>i. g i \<bind> (Tau \<circ> f) +\<^sub>f exit) =
          iter (f v \<bind> (Tau \<circ> g) +\<^sub>f exit \<bind> (Tau \<circ> f) +\<^sub>f exit) 
                     (\<lambda>i. g i \<bind> (Tau \<circ> f) +\<^sub>f exit)"
      apply (rule iter_cong_unrollL) 
      apply (auto simp: comp_def itree_simps)
      apply (rule bind_cong)
      by (auto split: sum.splits simp: itree_simps)
    then show ?case by blast
  next
    case (2 k)
    then show ?case by blast
  qed
next
  case io
  then show ?case by (auto elim!: itree_elims simp: bind_simps iter_simps) blast
qed

text \<open>
A nested iteration can be flattened to a single iteration given the result is unpacked
an extra level to trigger the continued progress.
\<close>
lemma iter_nest:
  "iter a (\<lambda>i. iter (f i) f) = iter a (\<lambda>i. f i \<bind> prog +\<^sub>f return)"
proof (coinduction arbitrary: a f rule: itree_coinduct)
  case ret
  then show ?case by (elim itree_elims; simp add: iter_simps)    
next
  case tau
  then show ?case
  proof ((elim itree_elims; simp add: iter_simps), goal_cases)
    case (1 v)
    have "iter (iter (f v) f) (\<lambda>i. iter (f i) f) = iter (f v \<bind> prog +\<^sub>f Ret) (\<lambda>i. iter (f i) f)"
      unfolding iter_unroll[of "f v \<bind> prog +\<^sub>f Ret"] iter_unroll[of "iter (f v) f"]
      unfolding iter_unroll[of "f v"] 
      apply (simp add: itree_simps)
      apply (rule bind_cong, blast)
      apply (auto split: sum.splits simp: itree_simps iter_unroll[symmetric])
      done
    then show ?case by blast
  next
    case (2 k)
    then show ?case by blast
  qed
next
  case io
  then show ?case by (elim itree_elims; simp add: iter_simps) blast
qed

subsection \<open>@{term ftp} Iteration\<close>

lemma iter_ftp [intro]:
  assumes "a \<leadsto> b"
  shows "iter a c \<leadsto> iter b c"
  using assms by induct (auto simp: iter_simps)

lemma iter_ftp_prog [intro]:
  assumes "a \<leadsto> prog v"
  shows "iter a c \<leadsto> iter (c v) c"
  using assms by induct (auto simp: iter_simps)

text \<open>
If we know an iteration consists of a prefix of @{term Tau} constructors to some new @{type itree},
this finite prefix may be derived from the current iteration or it may be a finite number of
iterations away. We introduce an inductive lemma to encode such conditions.
\<close>

lemma iter_ftp_induct_helper:
  assumes "iter a f \<leadsto> r" "f i \<leadsto> a"
  assumes "\<And>i r'. f i \<leadsto> r' \<Longrightarrow> iter r' f = r \<Longrightarrow> P i"
  assumes "\<And>i r j. P j \<Longrightarrow> f i \<leadsto> prog j \<Longrightarrow> P i"
  shows "P i"
  using assms(1,2,3)
proof (induct "iter a f" r arbitrary: a i)
  case (ftp_refl)
  then show ?case by blast
next
  case (ftp_tauI t' t)
  hence "iter a f = Tau t'" by auto
  thus ?case
  proof (cases rule: iter_TauE)
    case (nxt v)
    have "P v"
      apply (rule ftp_tauI(2)[OF nxt(2)])
      using ftp_tauI(5) by auto
    thus ?thesis using nxt ftp_tauI(4) assms(4) by blast
  next
    case (tau k)
    hence "f i \<leadsto> k" using ftp_tauI(4) ftp_trans by blast
    thus ?thesis using ftp_tauI(5) by (rule ftp_tauI(2)[OF tau(2)]) blast+
  qed
qed

lemma iter_ftp_induct_index[consumes 1, case_names base prog]:
  assumes "iter (f i) f \<leadsto> r"
  assumes "\<And>i r'. f i \<leadsto> r' \<Longrightarrow> iter r' f = r \<Longrightarrow> P i"
  assumes "\<And>i j. P j \<Longrightarrow> f i \<leadsto> prog j \<Longrightarrow> P i"
  shows "P i"
  using assms(2,3) iter_ftp_induct_helper[OF assms(1), of i]
  by blast

subsection \<open>Silent Iteration\<close>

text \<open>
We introduce a coinductive definition to capture the conditions for silent iteration, either:
  \<^item> An iteration is @{term silent}
  \<^item> A series of @{term prog} results that loop / never terminate
\<close>

coinductive nt_iter
  where 
    "a = silent \<Longrightarrow> nt_iter a f" |
    "a \<leadsto> prog v \<Longrightarrow> nt_iter (f v) f \<Longrightarrow> nt_iter a f"

subsubsection \<open>Deconstruction Properties\<close>

lemma nt_iter_simps [simp]:
  "nt_iter (IO e h) f = False"
  by (auto elim: nt_iter.cases)

lemma nt_iter_simps2 [simp]:
  "iter silent f = silent"
  by (subst iter_unroll) auto

subsubsection \<open>@{term nt_iter} Correctness\<close>

text \<open>
We demonstrate that @{term nt_iter} is equivalent to a @{term silent} iteration via
implication between the two.
\<close>

lemma iter_silentE:
  assumes "iter a f = silent"
  shows "nt_iter a f"
  using assms
proof (coinduction arbitrary: a)
  case nt_iter
  then show ?case
  proof (cases a rule: next_event)
    case inf
    then show ?thesis using nt_iter by auto
  next
    case (ret v)
    hence f: "iter a f \<leadsto> iter (return v) f" by auto
    show ?thesis
    proof (cases v)
      case (Inl l)
      hence "iter a f \<leadsto> iter (f l) f" using iter_ftp[OF ret] 
        by (metis ftp_refl ftp_tauI ftp_trans iter_simps(1) old.sum.simps(5))
      hence "iter (f l) f = silent" using nt_iter by auto
      then show ?thesis using Inl ret by blast
    next
      case (Inr b)
      then show ?thesis using nt_iter f by (auto simp: iter_simps)
    qed
  next
    case (io e c)
    hence "iter a f \<leadsto> iter (IO e c) f" by auto
    then show ?thesis using nt_iter by (auto simp: iter_simps) 
  qed
qed

lemma iter_silentI:
  assumes "nt_iter a f"
  shows "iter a f = silent"
  using assms
proof (coinduction arbitrary: a rule: itree.coinduct)
  case Eq_itree
  then show ?case
  proof (cases rule: nt_iter.cases)
    case 1
    then show ?thesis
      apply auto
      using Eq_itree by force
  next
    case (2 v)
    then show ?thesis
      apply auto
          apply (cases a rule: itree_sum_cases; auto)
      apply (cases a rule: itree_sum_cases; auto)
      apply (cases a rule: itree_sum_cases; auto)
      apply (cases a rule: itree_sum_cases; auto)
      using Eq_itree 
       apply (metis ftp.cases itree.distinct(1) itree.inject(2) nt_iter.intros(2))
      apply (cases a rule: itree_sum_cases; auto)
      done
  qed
qed

lemma nt_iter_correct:
  "(iter a f = silent) = (nt_iter a f)"
  using iter_silentI iter_silentE by blast

section \<open>Loop\<close>

text \<open>
Rephrasing of iteration into a more specific form, simply as the iteration of some function
given an initial state. Continuing from the concrete example earlier, this initial state would 
be the label for the entry block of a control flow graph.
\<close>

definition loop :: "('a \<Rightarrow> ('a+'b,'i,'o) itree) \<Rightarrow> 'a \<Rightarrow> ('b,'i,'o) itree"
  where "loop f \<equiv> \<lambda>i. iter (f i) f"

subsection \<open>Deconstruction Properties\<close>

lemma loop_simps [itree_simps]:
  "f i = exit v \<Longrightarrow> loop f i = Ret v"
  "f i = prog l \<Longrightarrow> loop f i = Tau (loop f l)"
  "f i = Tau k  \<Longrightarrow> loop f i = Tau (k \<bind> (\<lambda>i. Tau (loop f i)) +\<^sub>f Ret)"
  "f i = IO e c \<Longrightarrow> loop f i = IO e (\<lambda>i. c i \<bind> (\<lambda>i. Tau (loop f i)) +\<^sub>f Ret)"
  by (simp add: iter_simps loop_def comp_def iter_unroll[symmetric])+

lemma loop_RetE [itree_elims]:
  assumes "loop f i = Ret v"
  obtains "f i = exit v"
  using assms by (auto simp: loop_def elim: itree_elims)

lemma loop_TauE [itree_elims]:
  assumes "loop f i = Tau t"
  obtains (nxt) v where "f i = prog v" "t = loop f v" |
          (tau) k where "f i = Tau k" "t = k \<bind> (Tau o loop f) +\<^sub>f Ret"
  using assms iter_unroll by (auto simp: loop_def comp_def elim!: itree_elims)

lemma loop_IOE [itree_elims]:
  assumes "loop f i = IO e c"
  obtains (io) k where "f i = IO e k" "c = k ;; (Tau o loop f) +\<^sub>f Ret"
  using assms iter_unroll by (auto simp: loop_def comp_def elim!: itree_elims)

subsection \<open>@{term loop} Properties\<close>

text \<open>We replicate many of the @{term iter} properties for @{term loop}.\<close>

lemma loop_roll:
  "f ;; (tau ;; loop f) +\<^sub>f Ret = loop f" 
  apply (simp add: fun_eq_iff loop_def bind_simps)
  using iter_unroll by metis

lemma loop_unroll:
  "loop f i \<cong> f i \<bind> loop f +\<^sub>f return"
  apply (subst loop_roll[symmetric])
  apply (rule eutt_bindI)
  apply (rule eutt_refl)
  apply (intro allI)
  apply (case_tac b; simp add: itree_simps)
  by blast

lemma loop_bind:
  "loop m ;; b = loop (m ;; bimap return b)"
  using bind_iter unfolding loop_def by blast

lemma loop_rev:
  "loop (f ;; (tau ;; g) +\<^sub>f exit) = f ;; (tau ;; loop (g ;; (tau ;; f) +\<^sub>f exit)) +\<^sub>f return"
  using iter_rev[of "prog i" f g for i] iter_unroll unfolding fun_eq_iff  
  by (auto simp add: iter_simps loop_def bind_simps comp_def) 

lemma loop_nest:
  "loop (loop f) = loop (f ;; prog +\<^sub>f return)"
  using iter_nest[of "prog i" f for i] unfolding loop_def by (simp add: iter_simps)

lemma loop_exit:
  "loop (f ;; exit) = f"
  by (subst loop_roll[symmetric]) (auto simp: itree_simps)

lemma loop_emap:
  "loop f i \<oplus>\<guillemotleft>ot,it\<guillemotright> = loop (\<lambda>v. f v \<oplus>\<guillemotleft>ot,it\<guillemotright>) i"
  unfolding loop_def iter_emap by auto

section \<open>@{term eutt} Rules\<close>

text \<open>We can introduce an equivalence between two iterations trivially, if we can tie
their respective loop bodies together and maintain a fixed point throughout.
Intuitively, this struggles when considering fixed points that span multiple loop bodies.
\<close>

lemma eutt_iterI:
  assumes fp: "a \<approx>\<^bsub>d+\<^sub>pr\<^esub> b" "\<forall>a b. d a b \<longrightarrow> f a \<approx>\<^bsub>d+\<^sub>pr\<^esub> g b"
  shows "iter a f \<approx>\<^bsub>r\<^esub> iter b g"
  using fp
proof (coinduction arbitrary: a b rule: eutt_fp)
  case fp
  hence "euttF (d+\<^sub>pr) (gfp (euttF (d+\<^sub>pr))) aa ba" by (auto simp: eutt_peel)
  then show ?case unfolding iter_unroll[of aa] iter_unroll[of ba] 
  proof (rule euttF_bindI, goal_cases)
    case (1 l l')
    then show ?case using fp(2) by (auto split: sum.splits) blast
  next
    case (2 k1 k2)
    then show ?case using fp(2) unfolding iter_unroll[symmetric] eutt_def[symmetric] by blast
  qed
qed

lemma eutt_loopI:
  assumes "I i j"
  assumes "\<And>i j. I i j \<Longrightarrow> f i \<approx>\<^bsub>I+\<^sub>pE\<^esub> g j"
  shows "loop f i \<approx>\<^bsub>E\<^esub> loop g j"
proof (clarsimp simp: loop_def, intro eutt_iterI)
  show "f i \<approx>\<^bsub>I +\<^sub>p E\<^esub> g j" using assms by auto
next
  show "\<forall>a b. I a b \<longrightarrow> f a \<approx>\<^bsub>I +\<^sub>p E\<^esub> g b" using assms by auto
qed

end