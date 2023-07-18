theory Product
  imports Iteration Bisim Safety
begin

text \<open>
To facilitate reasoning over product programs, we introduce definitions to align
two @{type itree}s. The first of these aligns two trivial @{type itree}s, performing
simultaneous events and exits, with an abrupt exit if the structure cannot be aligned,
i.e. one @{type itree} is @{term silent} where the other is not.

This is then coupled with a notion of mutual progress through iteration, such
that we can take the product program of two @{term iter} @{type itree}s.
This notion of mutual progression must additionally handle the complications of
differences in loop bodies, inlining bodies until simultaneous events and exits
can be observed.
To support this, each inlining can only take place with the guarantee that
there will be an eventual event.

Overall goal with this work is the demonstration that @{term eutt} is equivalent
to a safety property over their product.
\<close>

section \<open>Product Program Construction\<close>

text \<open>
Synchronise events and @{term Tau} steps, with an early exit for mismatches on @{term silent}.\<close>
fun sync1
  where
    "sync1 (IO e\<^sub>1 k\<^sub>1, IO e\<^sub>2 k\<^sub>2) = IO (e\<^sub>1,e\<^sub>2) (\<lambda>(v\<^sub>1,v\<^sub>2). prog (k\<^sub>1 v\<^sub>1, k\<^sub>2 v\<^sub>2))" |
    "sync1 (Tau k\<^sub>1, Tau k\<^sub>2) = prog (k\<^sub>1, k\<^sub>2)" |
    "sync1 (Tau k\<^sub>1, k\<^sub>2) = (if k\<^sub>1 = silent then exit (k\<^sub>1, k\<^sub>2) else prog (k\<^sub>1,k\<^sub>2))" |
    "sync1 (k\<^sub>1, Tau k\<^sub>2) = (if k\<^sub>2 = silent then exit (k\<^sub>1, k\<^sub>2) else prog (k\<^sub>1,k\<^sub>2))" |
    "sync1 (k\<^sub>1,k\<^sub>2) = exit (k\<^sub>1,k\<^sub>2)"

text \<open>
We iterate @{term sync1} to obtain potentially infinite product construction via 
the @{term loop} operator.
\<close>
definition sync :: "('a, 'b, 'c) itree \<times> ('d, 'e, 'f) itree \<Rightarrow> 
                      (('a, 'b, 'c) itree \<times> ('d, 'e, 'f) itree, 'b \<times> 'e, 'c \<times> 'f) itree"
  where "sync \<equiv> loop sync1"

text \<open>
We continue iterations after @{term sync}ed loop bodies by calling iteration definitions
@{term f} and @{term g} where necessary. Careful handling of mismatched progression between
loop bodies is required, to capture conditions where one side may be @{term silent}.
In the event of behavioural mismatch, @{term None} is returned. Otherwise, the definition
returns the next @{type itree}s to synchronise or exits with the final simultaneous results.
\<close>
fun mutual_prog
  where 
    \<comment> \<open>Match silent internal behaviour\<close>
    "mutual_prog f g (prog l, prog r) = prog (f l, g r)" |
    "mutual_prog f g (prog l, Tau r) = prog (f l, Tau r)" |
    "mutual_prog f g (Tau l, prog r) = prog (Tau l, g r)" |
    "mutual_prog f g (Tau l, Tau r) = prog (Tau l, Tau r)" |

    \<comment> \<open>Synchronise progress across by demanding finite progression\<close>
    "mutual_prog f g (prog l, r) = (if iter (f l) f = silent then exit None else prog (f l, r))" |
    "mutual_prog f g (l, prog r) = (if iter (g r) g = silent then exit None else prog (l, g r))" |
    "mutual_prog f g (Tau t, r) = (if t = silent then exit None else prog (Tau t, r))" |
    "mutual_prog f g (l, Tau t) = (if t = silent then exit None else prog (l, Tau t))" | 

    \<comment> \<open>Match termination behaviour\<close>
    "mutual_prog f g (exit l, exit r) = exit (Some (l, r))" |
    "mutual_prog f g (exit _, IO _ _) = exit None" |
    "mutual_prog f g (IO _ _, exit _) = exit None" |

    "mutual_prog f g x = prog x"

text \<open>Loop the above to synchronise whole programs\<close>
abbreviation ksync
  where "ksync f g \<equiv> loop (sync ;; mutual_prog f g)"

subsection \<open>@{term sync} Properties\<close>

text \<open>
It is possible to establish @{term ftp} over a @{term sync} result given a @{term ftp} relation
over its arguments. This only holds if the new @{type itree} structure is not a @{term Tau},
as @{term sync} must evaluate @{term Tau}s simultaneously.
\<close>

lemma sync_ftpL:
  assumes "a \<leadsto> a'" "\<not> is_Tau a'"
  shows "sync (a,b) \<leadsto> sync (a',b)"
  using assms
proof (induct arbitrary: b)
  case 1
  then show ?case by blast
next
  case (2 t)
  thus ?case
  proof (cases b)
    case (Tau x2)
    have "x2 \<noteq> silent \<Longrightarrow> sync (a', b) = Tau (sync (a', x2))" using 2 Tau
      by (cases a'; auto simp: sync_def loop_def itree_simps)
    moreover have "sync (Tau t, b) = Tau (sync (t, x2))" 
      using Tau by (auto simp: sync_def loop_def itree_simps)
    ultimately show ?thesis using 2 Tau by (cases "x2 = silent"; auto simp: silent_fp)
  qed (insert 2; auto simp: sync_def loop_def itree_simps)+
qed

lemma sync_ftpR:
  assumes "b \<leadsto> b'" "\<not> is_Tau b'"
  shows "sync (a,b) \<leadsto> sync (a,b')"
  using assms
proof (induct arbitrary: a)
  case 1
  then show ?case by blast
next
  case (2 t)
  thus ?case
  proof (cases a)
    case (Tau x2)
    have "x2 \<noteq> silent \<Longrightarrow> sync (a, b') = Tau (sync (x2, b'))" using 2 Tau
      by (cases b'; auto simp: sync_def loop_def itree_simps)
    moreover have "sync (a, Tau t) = Tau (sync (x2, t))" 
      using Tau by (auto simp: sync_def loop_def itree_simps)
    ultimately show ?thesis using 2 Tau by (cases "x2 = silent"; auto simp: silent_fp)
  qed (insert 2; auto simp: sync_def loop_def itree_simps)+
qed

text \<open>@{term sync} over @{term silent} programs will itself be @{term silent}.\<close>

lemma sync1_silent [simp]:
  "sync1 (silent, silent) = prog (silent, silent)"
  using silent.code by (metis sync1.simps(2))

lemma sync_silent [simp]:
  "sync (silent, silent) = silent"
proof (coinduction)
  case ret
  then show ?case by (auto simp: sync_def elim!: itree_elims)
next
  case tau
  have g: "loop sync1 (silent, silent) = Tau (loop sync1 (silent, silent))"
    using loop_simps(2)[of sync1, OF sync1_silent] .
  show ?case using tau
    apply (auto simp: sync_def elim!: loop_TauE)
    using g by blast
next
  case io
  then show ?case by (auto simp: sync_def elim!: itree_elims)
qed 

lemma sync_simps [itree_simps]:
  \<comment> \<open>Event composition for @{term sync} is trivial\<close>
  "sync (return v, return v') = return (return v, return v')"
  "sync (return v, IO e' f')  = return (return v, IO e' f')"
  "sync (IO e f, return v')   = return (IO e f, return v')"
  "sync (IO e\<^sub>1 k\<^sub>1, IO e\<^sub>2 k\<^sub>2)   = IO (e\<^sub>1,e\<^sub>2) (\<lambda>(v\<^sub>1,v\<^sub>2). Tau (sync (k\<^sub>1 v\<^sub>1, k\<^sub>2 v\<^sub>2)))"

  \<comment> \<open>@{term Tau} composition progresses @{term sync} in the absence of @{term silent}\<close>
  "sync (Tau a, Tau b)                      = Tau (sync (a, b))"
  "k' \<noteq> silent \<Longrightarrow> sync (IO e f, Tau k')   = Tau (sync (IO e f, k'))"
  "k' \<noteq> silent \<Longrightarrow> sync (return v, Tau k') = Tau (sync (return v, k'))"
  "k \<noteq> silent  \<Longrightarrow> sync (Tau k, return v') = Tau (sync (k, return v'))"
  "k \<noteq> silent  \<Longrightarrow> sync (Tau k, IO e' f')  = Tau (sync (k, IO e' f'))"

  \<comment> \<open>Composition with @{term silent} immediately returns\<close>
  "sync (return v, silent)  = return (return v, silent)"
  "sync (silent, return v') = return (silent, return v')"
  "sync (silent, IO e' f')  = return (silent, IO e' f')"
  "sync (IO e f, silent)    = return (IO e f, silent)"

  by (auto simp: sync_def itree_simps loop_def)
     (subst silent.code; simp add: itree_simps)+

subsection \<open>@{term mutual_prog} Properties\<close>

text \<open>@{term mutual_prog} is trivially deconstructed by the implicit case analysis provided by
its definition. The only exception to this is the use of silent, which won't be matched.
We introduce the following to expand such conditions.\<close>

lemma mutual_prog_silentl [itree_simps]:
  "mutual_prog c\<^sub>1 c\<^sub>2 (silent, a) = (case a of prog v \<Rightarrow> prog (silent, c\<^sub>2 v) 
                                           | Tau k \<Rightarrow> prog (silent, Tau k) 
                                           | _ \<Rightarrow> exit None)"
  by (subst silent.code) (cases a rule: itree_sum_cases; auto)

lemma mutual_prog_silentr [itree_simps]:
  "mutual_prog c\<^sub>1 c\<^sub>2 (a, silent) = (case a of prog v \<Rightarrow> prog (c\<^sub>1 v, silent) 
                                           | Tau k \<Rightarrow> prog (Tau k, silent) 
                                           | _ \<Rightarrow> exit None)"
  by (subst silent.code) (cases a rule: itree_sum_cases; auto)

section \<open>Product Program Safety\<close>

text \<open>
Abbreviations to define the necessary safety condition to demonstrate equivalence between
these structures.
\<close>
abbreviation rel_some
  where "rel_some r \<equiv> \<lambda>a. (case a of None \<Rightarrow> False | Some (a,b) \<Rightarrow> r a b)"

abbreviation similar
  where "similar r \<equiv> safe r (\<lambda>(a,b). a = b) (\<lambda>_ (a,b). a = b) "

subsection \<open>Soundness\<close>

subsubsection \<open>Fixed Point Preservation\<close>

text \<open>
Similarity notion between programs serves as the fixed-point argument for program equivalence.
We demonstrate the preservation of this across the deconstruction of various mismatched
classes of structures.
\<close>

lemma similar_ftp:
  assumes "similar (rel_some r) (ksync c\<^sub>1 c\<^sub>2 (a, b))"
  assumes "(a \<leadsto> a' \<and> \<not> is_Tau a') \<or> a = a'"
  assumes "(b \<leadsto> b' \<and> \<not> is_Tau b') \<or> b = b'"
  shows "similar (rel_some r) (ksync c\<^sub>1 c\<^sub>2 (a', b'))"
proof -
  have "sync (a,b) \<leadsto> sync (a',b)"
    using assms(2) sync_ftpL by blast
  also have "... \<leadsto> sync (a',b')"
    using assms(3) sync_ftpR by blast
  finally have "ksync c\<^sub>1 c\<^sub>2 (a, b) \<leadsto> ksync c\<^sub>1 c\<^sub>2 (a',b')"
    unfolding loop_def by blast
  thus ?thesis using assms(1) safe_ftpI by blast
qed

lemma similar_tau_prog:
  assumes "similar (rel_some r) (ksync c\<^sub>1 c\<^sub>2 (Tau k, prog v))" (is "?S (Tau k) (prog v)")
  obtains a where "iter k c\<^sub>1 \<leadsto> iter a c\<^sub>1" "similar (rel_some r) (ksync c\<^sub>1 c\<^sub>2 (a, c\<^sub>2 v))"
proof (cases k rule: next_event)
  case inf
  then show ?thesis using assms that by (auto simp: itree_simps silent_fp) force
next
  case (ret v')
  show ?thesis
  proof (cases v')
    case (Inl a)
    hence "?S (prog a) (prog v)" using assms ret ftp_tauI by (auto intro: similar_ftp)
    moreover have "iter k c\<^sub>1 \<leadsto> iter (c\<^sub>1 a) c\<^sub>1" using ret Inl iter_ftp_prog by fast
    ultimately show ?thesis using that by (auto simp: itree_simps split: if_splits)
  next
    case (Inr b)
    hence "?S (exit b) (prog v)" using assms ret ftp_tauI by (auto intro: similar_ftp)
    then show ?thesis using iter_ftp Inr ret that 
      by (auto simp: itree_simps loop_def split: if_splits)
  qed
next
  case (io e f)
  hence "?S (IO e f) (prog v)" using assms ftp_tauI by (auto intro: similar_ftp)
  then show ?thesis using iter_ftp io that
    by (auto simp: itree_simps loop_def split: if_splits)
qed

lemma similar_prog_tau:
  assumes "similar (rel_some r) (ksync c\<^sub>1 c\<^sub>2 (prog v, Tau k))"
    (is "?S (Tau k) (prog v)")
  obtains a where "iter k c\<^sub>2 \<leadsto> iter a c\<^sub>2" 
      "similar (rel_some r) (ksync c\<^sub>1 c\<^sub>2 (c\<^sub>1 v, a))"
proof (cases k rule: next_event)
  case inf
  then show ?thesis using assms that by (auto simp: itree_simps silent_fp) force
next
  case (ret v')
  show ?thesis
  proof (cases v')
    case (Inl a)
    hence "?S (prog a) (prog v)" using assms ret ftp_tauI by (auto intro: similar_ftp)
    moreover have "iter k c\<^sub>2 \<leadsto> iter (c\<^sub>2 a) c\<^sub>2" using ret Inl iter_ftp_prog by fast
    ultimately show ?thesis using that by (auto simp: itree_simps loop_def split: if_splits)
  next
    case (Inr b)
    hence "?S (exit b) (prog v)" using assms ret ftp_tauI by (auto intro: similar_ftp)
    then show ?thesis using iter_ftp Inr ret that 
      by (auto simp: itree_simps loop_def split: if_splits)
  qed
next
  case (io e f)
  hence "?S (IO e f) (prog v)" using assms ftp_tauI by (auto intro: similar_ftp)
  then show ?thesis using iter_ftp io that
    by (auto simp: itree_simps loop_def split: if_splits)
qed

lemma similar_event_prog:
  assumes "similar (rel_some r) (ksync c\<^sub>1 c\<^sub>2 (a, prog v))"
  assumes "\<not>is_Tau a \<and> (is_Ret a \<longrightarrow> \<not> isl (un_Ret a))"
  shows "similar (rel_some r) (ksync c\<^sub>1 c\<^sub>2 (a,c\<^sub>2 v))"
  using assms 
  by (cases a rule: itree_sum_cases; auto simp: itree_simps loop_def split: if_splits)

lemma similar_prog_event:
  assumes "similar (rel_some r) (ksync c\<^sub>1 c\<^sub>2 (prog v, a))"
  assumes "\<not>is_Tau a \<and> (is_Ret a \<longrightarrow> \<not> isl (un_Ret a))"
  shows "similar (rel_some r) (ksync c\<^sub>1 c\<^sub>2 (c\<^sub>1 v,a))"
  using assms 
  by (cases a rule: itree_sum_cases; auto simp: itree_simps loop_def split: if_splits)

lemma similar_event_tau:
  assumes "similar (rel_some r) (ksync c\<^sub>1 c\<^sub>2 (a, Tau k))"
  assumes "\<not>is_Tau a \<and> (is_Ret a \<longrightarrow> \<not> isl (un_Ret a))"
  shows "similar (rel_some r) (ksync c\<^sub>1 c\<^sub>2 (a,k))"
  using assms 
  by (cases a rule: itree_sum_cases; cases "k = silent") 
     (auto simp: itree_simps loop_def silent_fp split: if_splits)

lemma similar_tau_event:
  assumes "similar (rel_some r) (ksync c\<^sub>1 c\<^sub>2 (Tau k,a))"
  assumes "\<not>is_Tau a \<and> (is_Ret a \<longrightarrow> \<not> isl (un_Ret a))"
  shows "similar (rel_some r) (ksync c\<^sub>1 c\<^sub>2 (k,a))"
  using assms 
  by (cases a rule: itree_sum_cases; cases "k = silent") 
     (auto simp: itree_simps loop_def silent_fp split: if_splits)

lemma similar_tau_tau:
  assumes "similar (rel_some r) (ksync c\<^sub>1 c\<^sub>2 (Tau k,Tau k'))"
  obtains "similar (rel_some r) (ksync c\<^sub>1 c\<^sub>2 (k,k'))"
  using assms unfolding loop_def by (auto simp: itree_simps)

lemma similar_io_io:
  assumes "similar (rel_some r) (ksync c\<^sub>1 c\<^sub>2 (IO e f,IO e' f'))"
  obtains "e = e'" "\<forall>v. similar (rel_some r) (ksync c\<^sub>1 c\<^sub>2 (f v,f' v))"
  using assms unfolding loop_def by (auto simp: itree_simps)

lemma similar_silent:
  assumes "nt_iter a c\<^sub>1"
  assumes "similar (rel_some r) (loop (sync ;; mutual_prog c\<^sub>1 c\<^sub>2) (a,b))" (is "?FP a b")
  shows "nt_iter b c\<^sub>2"
  using assms
proof (coinduction arbitrary: a b)
  case nt_iter
  hence s: "similar (rel_some r) (iter (sync (a, b) \<bind> mutual_prog c\<^sub>1 c\<^sub>2) 
                (\<lambda>i. sync i \<bind> mutual_prog c\<^sub>1 c\<^sub>2))" (is "?F (sync (a,b))")
    by (auto simp: loop_def)

  show ?case using nt_iter(1)
  proof (cases rule: nt_iter.cases)
    case 1
    show ?thesis using nt_iter
    proof (cases b rule: next_event)
      case (ret v)
      hence s: "similar (rel_some r) (ksync c\<^sub>1 c\<^sub>2 (silent,return v))"
        using nt_iter(2) similar_ftp 1 by fastforce
      thus ?thesis using ret 1 nt_iter by (cases v) (auto simp: itree_simps)
    next
      case (io e f)
      hence "similar (rel_some r) (ksync c\<^sub>1 c\<^sub>2 (silent,IO e f))"
        using nt_iter(2) similar_ftp 1 by fastforce
      then show ?thesis by (auto simp: itree_simps)
    qed auto
  next
    case (2 v)
    then show ?thesis 
    proof (cases b rule: next_event)
      case (ret v')
      hence "similar (rel_some r) (ksync c\<^sub>1 c\<^sub>2 (prog v,return v'))"
        using nt_iter(2) similar_ftp 2(1) by fastforce
      then show ?thesis using 2 ret
        by (cases v') (auto simp: itree_simps nt_iter_correct loop_def split: if_splits)        
    next
      case (io e f)
      hence "similar (rel_some r) (ksync c\<^sub>1 c\<^sub>2 (prog v,IO e f))"
        using nt_iter(2) similar_ftp 2(1) by fastforce
      then show ?thesis using 2
        by (auto simp: itree_simps nt_iter_correct loop_def split: if_splits)
    qed auto
  qed
qed

lemma similar_silent':
  assumes "nt_iter a c\<^sub>1"
  assumes "similar (rel_some r) (loop (sync ;; mutual_prog c\<^sub>2 c\<^sub>1) (b,a))" (is "?FP a b")
  shows "nt_iter b c\<^sub>2"
  using assms
proof (coinduction arbitrary: a b)
  case nt_iter
  hence s: "similar (rel_some r) (iter (sync (b, a) \<bind> mutual_prog c\<^sub>2 c\<^sub>1) 
                (\<lambda>i. sync i \<bind> mutual_prog c\<^sub>2 c\<^sub>1))" (is "?F (sync (a,b))")
    by (auto simp: loop_def)

  show ?case using nt_iter(1)
  proof (cases rule: nt_iter.cases)
    case 1
    show ?thesis using nt_iter
    proof (cases b rule: next_event)
      case (ret v)
      hence s: "similar (rel_some r) (ksync c\<^sub>2 c\<^sub>1 (return v,silent))"
        using nt_iter(2) similar_ftp 1 by fastforce
      thus ?thesis using ret 1 nt_iter by (cases v) (auto simp: itree_simps)
    next
      case (io e f)
      hence "similar (rel_some r) (ksync c\<^sub>2 c\<^sub>1 (IO e f,silent))"
        using nt_iter(2) similar_ftp 1 by fastforce
      then show ?thesis by (auto simp: itree_simps)
    qed auto
  next
    case (2 v)
    then show ?thesis 
    proof (cases b rule: next_event)
      case (ret v')
      hence "similar (rel_some r) (ksync c\<^sub>2 c\<^sub>1 (return v',prog v))"
        using nt_iter(2) similar_ftp 2(1) by fastforce
      then show ?thesis using 2 ret
        by (cases v') (auto simp: itree_simps nt_iter_correct loop_def split: if_splits)        
    next
      case (io e f)
      hence "similar (rel_some r) (ksync c\<^sub>2 c\<^sub>1 (IO e f,prog v))"
        using nt_iter(2) similar_ftp 2(1) by fastforce
      then show ?thesis using 2
        by (auto simp: itree_simps nt_iter_correct loop_def split: if_splits)
    qed auto
  qed
qed

text \<open>
The soundness result for safety over the product. Shown by a coinduction proof in which
we align their divergence behaviour, maintain the fixed-point over finite @{term Tau}s
and then demonstrate the consequences of the fixed-point over the events.
\<close>
lemma product_sound:
  assumes "similar (rel_some r) (ksync c\<^sub>1 c\<^sub>2 (a,b))"
  shows "iter a c\<^sub>1 \<approx>\<^bsub>r\<^esub> iter b c\<^sub>2"
  using assms
proof (coinduction arbitrary: a b rule: eutt_sync)
  case sil
  then show ?case using similar_silent similar_silent' nt_iter_correct by metis
next
  case ret
  then show ?case 
    by (cases ba rule: itree_sum_cases; auto elim!: itree_elims simp: itree_simps)
next
  case io
  then show ?case 
    by (cases ba rule: itree_sum_cases; auto elim!: itree_elims similar_io_io simp: itree_simps)
next
  case both
  then show ?case by (auto elim!: itree_elims similar_prog_tau similar_tau_prog similar_tau_tau 
                           simp: itree_simps) fast
next
  case left
  then show ?case  
    by (auto elim!: itree_elims simp: itree_simps intro: similar_event_prog similar_event_tau)
next
  case right
  then show ?case
    by (auto elim!: itree_elims simp: itree_simps intro: similar_prog_event similar_tau_event)
qed

subsection \<open>Completeness\<close>

text \<open>We demonstrate completeness by showing that each iteration @{term ksync} will
produce a pair of equivalent @{type itree}s. The proof is considerably simpler by using
the coinductive form for @{term safe} that skips to the next event. We introduce the
following abbreviation to encapsulate the necessary conditions for this coinduction to hold.\<close>

abbreviation outcome 
  where "outcome a b c\<^sub>1 c\<^sub>2 r \<equiv> sync (a, b) \<bind> mutual_prog c\<^sub>1 c\<^sub>2 = silent \<or>
    (\<exists>v. sync (a, b) \<bind> mutual_prog c\<^sub>1 c\<^sub>2 \<leadsto> return v \<and>
         ((\<lambda>(a, b). iter a c\<^sub>1 \<approx>\<^bsub>r\<^esub> iter b c\<^sub>2) +\<^sub>f rel_some r) v) \<or>
    (\<exists>e f. sync (a, b) \<bind> mutual_prog c\<^sub>1 c\<^sub>2 \<leadsto> IO e f \<and>
           (case e of (x, xa) \<Rightarrow> x = xa) \<and>
           (\<forall>v. (case v of (x, xa) \<Rightarrow> x = xa) \<longrightarrow>
                (\<exists>a b. f v = sync (a, b) \<bind> mutual_prog c\<^sub>1 c\<^sub>2 \<and>
                       iter a c\<^sub>1 \<approx>\<^bsub>r\<^esub> iter b c\<^sub>2) \<or>
                similar ((\<lambda>(a, b). iter a c\<^sub>1 \<approx>\<^bsub>r\<^esub> iter b c\<^sub>2) +\<^sub>f rel_some r) (f v)))"

lemma product_step_exit:
  assumes "iter (exit l) c\<^sub>1 \<approx>\<^bsub>r\<^esub> iter b c\<^sub>2" "\<not>is_Tau b"
  shows "outcome (exit l) b c\<^sub>1 c\<^sub>2 r"
  using assms by (cases b rule: itree_sum_cases; auto elim!: eutt_elims simp: itree_simps)

lemma product_step_io:
  assumes "iter (IO e f) c\<^sub>1 \<approx>\<^bsub>r\<^esub> iter b c\<^sub>2" "\<not>is_Tau b"
  shows "outcome (IO e f) b c\<^sub>1 c\<^sub>2 r"
  using assms 
proof (cases b rule: itree_sum_cases)
  case (io e' f')
  have "sync (IO e f, IO e' f') \<bind> mutual_prog c\<^sub>1 c\<^sub>2 \<leadsto> 
        IO (e,e') (\<lambda>(v,v'). Tau (sync (f v, f' v') \<bind> mutual_prog c\<^sub>1 c\<^sub>2))"
    by (auto simp: itree_simps)
  moreover have "e = e'" "\<forall>v. (\<lambda>(v,v'). Tau (sync (f v, f' v') \<bind> mutual_prog c\<^sub>1 c\<^sub>2)) (v,v) = sync (Tau (f ( v)), Tau (f' ( v))) \<bind> mutual_prog c\<^sub>1 c\<^sub>2 \<and>
                   iter (Tau (f ( v))) c\<^sub>1 \<approx>\<^bsub>r\<^esub> iter (Tau (f' ( v))) c\<^sub>2"
    using assms io by (auto simp: itree_simps elim!: eutt_elims)
  ultimately show ?thesis unfolding io by blast
qed (auto elim!: eutt_elims simp: itree_simps)

lemma product_silent_prog:
  assumes "iter silent c\<^sub>1 \<approx>\<^bsub>r\<^esub> iter b c\<^sub>2"
  shows "outcome silent b c\<^sub>1 c\<^sub>2 r"
proof -
  have "nt_iter b c\<^sub>2" using assms nt_iter_correct by auto
  thus ?thesis
  proof (cases rule: nt_iter.cases)
    case 1
    then show ?thesis by (auto simp: itree_simps)
  next
    case (2 v)
    hence "sync (silent, b) \<bind> mutual_prog c\<^sub>1 c\<^sub>2 \<leadsto> sync (silent, prog v) \<bind> mutual_prog c\<^sub>1 c\<^sub>2" 
      using sync_ftpR by force
    moreover have "sync (silent, prog v) \<bind> mutual_prog c\<^sub>1 c\<^sub>2 = prog (silent, c\<^sub>2 v)"
      by (auto simp: itree_simps)
    moreover have "iter silent c\<^sub>1 \<approx>\<^bsub>r\<^esub> iter (c\<^sub>2 v) c\<^sub>2"
      using 2 by (auto simp: nt_iter_correct)
    ultimately show ?thesis by auto
  qed
qed

lemma product_silent_prog':
  assumes "iter a c\<^sub>1 \<approx>\<^bsub>r\<^esub> iter silent c\<^sub>2"
  shows "outcome a silent c\<^sub>1 c\<^sub>2 r"
proof -
  have "nt_iter a c\<^sub>1" using assms nt_iter_correct by auto
  thus ?thesis
  proof (cases rule: nt_iter.cases)
    case 1
    then show ?thesis by (auto simp: itree_simps)
  next
    case (2 v)
    hence "sync (a, silent) \<bind> mutual_prog c\<^sub>1 c\<^sub>2 \<leadsto> sync (prog v, silent) \<bind> mutual_prog c\<^sub>1 c\<^sub>2" 
      using sync_ftpL by force
    moreover have "sync (prog v, silent) \<bind> mutual_prog c\<^sub>1 c\<^sub>2 = prog (c\<^sub>1 v, silent)"
      by (auto simp: itree_simps)
    moreover have "iter (c\<^sub>1 v) c\<^sub>1 \<approx>\<^bsub>r\<^esub> iter silent c\<^sub>2"
      using 2 by (auto simp: nt_iter_correct)
    ultimately show ?thesis by auto
  qed
qed

lemma product_step_prog:
  assumes "iter (prog l) c\<^sub>1 \<approx>\<^bsub>r\<^esub> iter b c\<^sub>2" "\<not>is_Tau b"
  shows "outcome (prog l) b c\<^sub>1 c\<^sub>2 r"
proof (cases "iter (c\<^sub>1 l) c\<^sub>1 = silent")
  case True
  hence "nt_iter b c\<^sub>2" using assms nt_iter_correct by (auto simp: itree_simps silent_fp)
  thus ?thesis
  proof (cases rule: nt_iter.cases)
    case 1
    thus ?thesis using assms by (auto simp: itree_simps)
  next
    case (2 v)
    hence "sync (prog l, b) \<bind> mutual_prog c\<^sub>1 c\<^sub>2 \<leadsto> sync (prog l, prog v) \<bind> mutual_prog c\<^sub>1 c\<^sub>2" 
      using sync_ftpR ftp_trans by (smt (verit, ccfv_SIG) bind_ftp itree.disc(4))
    moreover have "sync (prog l, prog v) \<bind> mutual_prog c\<^sub>1 c\<^sub>2 = prog (c\<^sub>1 l, c\<^sub>2 v)"
      by (auto simp: itree_simps)
    moreover have "iter (c\<^sub>1 l) c\<^sub>1 \<approx>\<^bsub>r\<^esub> iter (c\<^sub>2 v) c\<^sub>2"
      using assms 2 by (auto simp: itree_simps)
    ultimately show ?thesis using assms 2 by (auto)
  qed
next
  case False
  hence t: "iter (c\<^sub>1 l) c\<^sub>1 \<noteq> silent" by auto
  then show ?thesis 
  proof (cases "\<exists>l'. b = prog l'")
    case True
    then show ?thesis using assms(1) by (auto simp: itree_simps) blast
  next
    case False
    hence "sync (prog l, b) \<bind> mutual_prog c\<^sub>1 c\<^sub>2 = prog (c\<^sub>1 l, b)"
      using assms(2) t by (cases b rule: itree_sum_cases; auto simp: itree_simps)
    thus ?thesis using assms(1) by (auto simp: itree_simps)
  qed
qed

lemma product_step_complete:
  assumes "iter a c\<^sub>1 \<approx>\<^bsub>r\<^esub> iter b c\<^sub>2"
  shows "similar ((\<lambda>(a, b). iter a c\<^sub>1 \<approx>\<^bsub>r\<^esub> iter b c\<^sub>2) +\<^sub>f rel_some r) (sync (a, b) \<bind> mutual_prog c\<^sub>1 c\<^sub>2)"
  using assms
proof (coinduction arbitrary: a b rule: safe_event_coinduct[case_names safe])
  case safe
  consider "aa = silent" | "b = silent" | "aa \<noteq> silent" "b \<noteq> silent" by auto
  then show ?case 
  proof (cases)
    case 1
    then show ?thesis using product_silent_prog[OF safe[simplified 1]] by blast
  next
    case 2
    then show ?thesis using product_silent_prog'[OF safe[simplified 2]] by blast
  next
    case 3
    then obtain a' where a': "aa \<leadsto> a'" "\<not> is_Tau a'" 
      by (cases aa rule: next_event; auto)
    obtain b' where b': "b \<leadsto> b'" "\<not> is_Tau b'" 
      using 3 safe by (cases b rule: next_event; auto)
    hence s: "sync (aa, b) \<bind> mutual_prog c\<^sub>1 c\<^sub>2 \<leadsto> sync (a', b') \<bind> mutual_prog c\<^sub>1 c\<^sub>2" 
      using a' by (meson bind_ftp ftp_trans itree.disc(4) itree.disc(6) sync_ftpL sync_ftpR) 
    have eq: "iter a' c\<^sub>1 \<approx>\<^bsub>r\<^esub> iter b' c\<^sub>2" using a' b' safe by auto

    hence "outcome a' b' c\<^sub>1 c\<^sub>2 r"
    proof (cases a' rule: itree_sum_cases)
      case (left i)
      then show ?thesis using product_step_prog[OF eq[simplified left]] b' by simp
    next
      case (right v)
      then show ?thesis using product_step_exit[OF eq[simplified right]] b' by simp
    next
      case (io e f)
      then show ?thesis using product_step_io[OF eq[simplified io]] b' by simp
    next
      case (tau k)
      then show ?thesis using a' by auto
    qed

    thus ?thesis using ftp_trans[OF s] by auto 
  qed
qed

lemma product_complete:
  assumes "iter a c\<^sub>1 \<approx>\<^bsub>r\<^esub> iter b c\<^sub>2"
  shows "similar (rel_some r) (ksync c\<^sub>1 c\<^sub>2 (a,b))"
  using assms
proof (coinduction arbitrary: a b rule: safe_loop)
  case inv
  then show ?case using product_step_complete by force
qed

subsection \<open>Correctness\<close>

text \<open>Given these outcomes, @{term eutt} over two iterations is equivalent to a safety property
over their product.\<close>

theorem product_correct:
  "similar (rel_some r) (ksync c\<^sub>1 c\<^sub>2 (a,b)) = (iter a c\<^sub>1 \<approx>\<^bsub>r\<^esub> iter b c\<^sub>2)"
  using product_complete product_sound by metis

end