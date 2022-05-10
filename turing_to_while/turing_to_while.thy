theory turing_to_while
  imports Main "Turing" "../IMP-/Com" "../IMP-/Big_StepT" "../IMP-/Small_StepT" "../IMP-/Big_Step_Small_Step_Equivalence"  "../IMP-/Max_Constant" "../fresh_names/Fresh_Class" "tape_nat_conversion"

begin
subsection "Encoding of Tape Instructions As arithmetic Operations"
text "The encoding of the tape into a natural number as well as the encoding of the operations as functions on natural numbers is taken from https://www21.in.tum.de/teaching/theo/SS19/folien-handout.pdf ."
abbreviation LeftShift:: "atomExp \<Rightarrow> aexp" ("_\<lless>") where
"LeftShift a \<equiv> Plus a a"

fun encode_tape_instr :: "action  \<Rightarrow> com" where
"encode_tape_instr a = (case a of Nop \<Rightarrow> SKIP |
                                  W0 \<Rightarrow> ''y''::= (V ''y''\<then>);;''y''::= (V ''y''\<lless>) |
                                  W1 \<Rightarrow> ''y''::= (V ''y''\<then>);;''y''::=(V ''y''\<lless>);;''y''::= ((V ''y'') \<oplus> (N 1)) |
                                  L \<Rightarrow> ''y''::= (V ''y''\<lless>);;''t''::=(V ''x''\<doteq>1);;''y''::= ((V ''y'') \<oplus> (V ''t''));; ''x''::= (V ''x''\<then>) |
                                  R \<Rightarrow> ''x''::= (V ''x''\<lless>);;''t''::=(V ''y''\<doteq>1);;''x''::= ((V ''x'') \<oplus> (V ''t''));;''y''::= (V ''y''\<then>))"
lemma encode_tape_instr_cost:
  assumes encode_instr: "((encode_tape_instr i),s0) \<Rightarrow>\<^bsup> k \<^esup> s"
  shows " 1 \<le> k \<and> k \<le> 8" 
 using assms proof (cases i)
  case W0
  then show ?thesis using encode_instr by fastforce
next
  case W1
  then show ?thesis using encode_instr by fastforce
next
  case L
  then show ?thesis using encode_instr by fastforce
next
  case R
  then show ?thesis using encode_instr by fastforce
next
  case Nop
  then show ?thesis using encode_instr by fastforce
qed

lemma rightShift_state: 
  assumes rightShift_com: "(v::= (V v\<then>), s) \<Rightarrow>\<^bsup> k \<^esup> s'"
  shows " (s v) div 2 = s' v" 
  using assms proof -
   show ?thesis using rightShift_com by auto
 qed

lemma encode_w0_x: 
  assumes encode_w0: "(c;;(encode_tape_instr W0),s0) \<Rightarrow>\<^bsup> k \<^esup> s"
    and encode_instr: "(c,s0) \<Rightarrow>\<^bsup> k' \<^esup> s'"
shows "s ''x'' = s' ''x''"
  using assms proof -
  obtain k' s1 k'' where "(c,s0) \<Rightarrow>\<^bsup> k' \<^esup> s1" and
         "(encode_tape_instr W0,s1) \<Rightarrow>\<^bsup> k'' \<^esup> s" using encode_w0 by blast 
  then have "s1 = s'" using big_step_t_determ2 encode_instr by blast
  have "''x'' \<notin> set (Max_Constant.all_variables (encode_tape_instr W0))" by simp
  then show ?thesis
    by (metis \<open>(encode_tape_instr W0, s1) \<Rightarrow>\<^bsup> k'' \<^esup> s\<close> \<open>s1 = s'\<close> com_only_vars)
qed

lemma encode_w0_y: 
  assumes encode_w0: "(c;;(encode_tape_instr W0),s0) \<Rightarrow>\<^bsup> k \<^esup> s"
    and encode_instr: "(c,s0) \<Rightarrow>\<^bsup> k' \<^esup> s'"
shows "s ''y'' = (if even (s' ''y'') then s' ''y'' else s' ''y'' - 1)"
  using assms proof -
  obtain k' s1 k'' where "(c,s0) \<Rightarrow>\<^bsup> k' \<^esup> s1" and
         "(encode_tape_instr W0,s1) \<Rightarrow>\<^bsup> k'' \<^esup> s" and
         "k'' = 4" using encode_w0 by fastforce
  then have "s1 = s'" using big_step_t_determ2 encode_instr by blast
  have "k' + k'' = k"
    by (meson Seq \<open>(c, s0) \<Rightarrow>\<^bsup> k' \<^esup> s1\<close> \<open>(encode_tape_instr W0, s1) \<Rightarrow>\<^bsup> k'' \<^esup> s\<close> big_step_t_determ2 encode_w0)
  from encode_w0 have "(c;;''y''::= (V ''y''\<then>);;''y''::= (V ''y''\<lless>),s0) \<Rightarrow>\<^bsup> k \<^esup> s" by fastforce
  have "(c;;''y''::= (V ''y''\<then>);;''y''::= Plus (V ''y'') (V ''y''),s0) \<Rightarrow>\<^bsup> k \<^esup> s1(''y'' := LeftShift_nat (s1 ''y'' div 2))" 
    apply(rule Seq) apply(rule Seq) apply(auto) apply(fact) apply(rule AssignI) using \<open>k' + k'' = k\<close> \<open>k'' = 4\<close> by auto
  then show ?thesis by (metis \<open>(c;; ''y'' ::= (V ''y''\<then>);; ''y'' ::= V ''y''\<lless>, s0) \<Rightarrow>\<^bsup> k \<^esup> s\<close> \<open>s1 = s'\<close> big_step_t_determ2 dvd_mult_div_cancel fun_upd_same mult_2 odd_two_times_div_two_nat)
qed

lemma update_encode_w0:
  assumes encode_w0: "((encode_tape_instr W0),s0) \<Rightarrow>\<^bsup> k \<^esup> s"
  assumes update_w0: "(l,r) = update W0 (l0,r0)"
  and tape_state_eq: "s0 ''x'' = tape_to_nat l0 \<and> s0 ''y'' = tape_to_nat r0"
shows "s ''x'' = tape_to_nat l" "s ''y'' = tape_to_nat r" 
proof -
    from encode_w0 encode_w0_x tape_state_eq update_w0 show "s ''x'' = tape_to_nat l" by auto
  next
    from encode_w0 encode_w0_y have "s ''y'' = (if even (s0 ''y'') then s0 ''y'' else s0 ''y'' - 1)" by blast
    then have "s ''y'' = (if even (tape_to_nat r0) then tape_to_nat r0 else tape_to_nat r0 - 1)" using tape_state_eq by simp          
    also have "(if even (tape_to_nat r0) then tape_to_nat r0 else tape_to_nat r0 - 1) = tape_to_nat r" proof (cases "even (tape_to_nat r0)")
      case True
      then have "Bk#tl r0 = r0 \<or> r0 = []" using tape_to_nat_even list.collapse by force
      moreover have "r0 = [] \<Longrightarrow> tape_to_nat r0 = tape_to_nat r" using update_w0 by auto
      moreover have "r0 = Bk#tl r0 \<Longrightarrow> tape_to_nat r0 = tape_to_nat r" using update_w0 by auto
      ultimately have "tape_to_nat r0 = tape_to_nat r" by auto
      then show ?thesis using True by auto
    next
      case False
      then have "Oc#tl r0 = r0" using list.collapse tape_to_nat_even tape_to_nat_odd by fastforce
      also have "Bk#tl r0 = r" using update_w0 by auto
      ultimately have "tape_to_nat r0 - 1 = tape_to_nat r"
        by (metis add_implies_diff cell.distinct(1) tape_to_nat.simps(2))
      then show ?thesis using False by auto
    qed
    finally show "s ''y'' = tape_to_nat r" by auto
  qed

lemma encode_w1_x: 
  assumes encode_w1: "(c;;(encode_tape_instr W1),s0) \<Rightarrow>\<^bsup> k \<^esup> s"
    and encode_instr: "(c,s0) \<Rightarrow>\<^bsup> k' \<^esup> s'"
shows "s ''x'' = s' ''x''"
  using assms proof -
  obtain k' s1 k'' where "(c,s0) \<Rightarrow>\<^bsup> k' \<^esup> s1" and
         "(encode_tape_instr W1,s1) \<Rightarrow>\<^bsup> k'' \<^esup> s" using encode_w1 by blast 
  then have "s1 = s'" using big_step_t_determ2 encode_instr by blast
  have "''x'' \<notin> set (Max_Constant.all_variables (encode_tape_instr W1))" by simp                         
  then show ?thesis
    by (metis \<open>(encode_tape_instr W1, s1) \<Rightarrow>\<^bsup> k'' \<^esup> s\<close> \<open>s1 = s'\<close> com_only_vars)
qed

lemma encode_w1_y: (* also provable by showing it is simply Suc W0 *)
  assumes encode_w1: "(c;;(encode_tape_instr W1),s0) \<Rightarrow>\<^bsup> k \<^esup> s"
    and encode_instr: "(c,s0) \<Rightarrow>\<^bsup> k' \<^esup> s'"
shows "s ''y'' = (if even (s' ''y'') then s' ''y'' + 1 else s' ''y'')"
  using assms proof -
  obtain k' s1 k'' where "(c,s0) \<Rightarrow>\<^bsup> k' \<^esup> s1" and
         "(encode_tape_instr W1,s1) \<Rightarrow>\<^bsup> k'' \<^esup> s" and
         "k'' = 6" using encode_w1 by fastforce
  then have "s1 = s'" using big_step_t_determ2 encode_instr by blast
  have "k' + k'' = k"
    by (meson Seq \<open>(c, s0) \<Rightarrow>\<^bsup> k' \<^esup> s1\<close> \<open>(encode_tape_instr W1, s1) \<Rightarrow>\<^bsup> k'' \<^esup> s\<close> big_step_t_determ2 encode_w1)
  from encode_w1 have "(c;;''y''::= (V ''y''\<then>);;''y''::= (V ''y''\<lless>);;''y''::= ((V ''y'') \<oplus> (N 1)),s0) \<Rightarrow>\<^bsup> k \<^esup> s" by fastforce
  have "(c;;''y''::= (V ''y''\<then>);;''y''::= Plus (V ''y'') (V ''y'');;''y''::= ((V ''y'') \<oplus> (N 1)),s0) \<Rightarrow>\<^bsup> k \<^esup>s1(''y'' := Suc (LeftShift_nat (s1 ''y'' div 2)))" 
    apply(rule Seq) apply(rule Seq) apply(rule Seq) apply(auto) apply(fact) apply(rule AssignI) using \<open>k' + k'' = k\<close> \<open>k'' = 6\<close> by auto
  then show ?thesis
    by (smt (verit, del_insts) Suc_eq_plus1 \<open>(c;; ''y'' ::= (V ''y''\<then>);; ''y'' ::= V ''y''\<lless>;; ''y'' ::= (V ''y'' \<oplus> N 1), s0) \<Rightarrow>\<^bsup> k \<^esup> s\<close> \<open>s1 = s'\<close> add_self_div_2 bigstep_det bit_eq_rec even_add even_succ_div_2 fun_upd_same odd_one plus_1_eq_Suc)
  qed

lemma update_encode_w1:
  assumes encode_w1: "((encode_tape_instr W1),s0) \<Rightarrow>\<^bsup> k \<^esup> s"
  assumes update_w1: "(l,r) = update W1 (l0,r0)"
  and tape_state_eq: "s0 ''x'' = tape_to_nat l0 \<and> s0 ''y'' = tape_to_nat r0"
shows "s ''x'' = tape_to_nat l" "s ''y'' = tape_to_nat r" 
proof -
    from encode_w1 encode_w0_x tape_state_eq update_w1 show "s ''x'' = tape_to_nat l" by auto
  next
    from encode_w1 encode_w1_y have "s ''y'' = (if even (s0 ''y'') then s0 ''y'' + 1 else s0 ''y'')" by blast
    then have "s ''y'' = (if even (tape_to_nat r0) then tape_to_nat r0 + 1 else tape_to_nat r0)" using tape_state_eq by simp          
    also have "(if even (tape_to_nat r0) then tape_to_nat r0 + 1 else tape_to_nat r0) = tape_to_nat r" proof (cases "even (tape_to_nat r0)")
      case True
      then have "Bk#tl r0 = r0 \<or> r0 = []" using tape_to_nat_even list.collapse by force
      moreover have "r0 = [] \<Longrightarrow> tape_to_nat r0 + 1 = tape_to_nat r" using update_w1 by auto
      moreover have "r0 = Bk#tl r0 \<Longrightarrow> tape_to_nat r0 + 1 = tape_to_nat r" using update_w1
        by (metis Turing.update.simps(2) cell.distinct(1) prod.inject tape_to_nat.simps(2))
      ultimately have "tape_to_nat r0 + 1 = tape_to_nat r" by auto
      then show ?thesis using True by auto
    next
      case False
      then have "Oc#tl r0 = r0" using list.collapse tape_to_nat_even tape_to_nat_odd by fastforce
      then have "r0 = r" using update_w1 by simp
      then show ?thesis using False by auto
    qed
    finally show "s ''y'' = tape_to_nat r" by auto
  qed

lemma encode_L_x: 
  assumes encode_L: "(c;;(encode_tape_instr L),s0) \<Rightarrow>\<^bsup> k \<^esup> s"
    and encode_instr: "(c,s0) \<Rightarrow>\<^bsup> k' \<^esup> s'"
shows "s ''x'' = s' ''x'' div 2"
  using assms proof -
  obtain k' s1 k'' where "(c,s0) \<Rightarrow>\<^bsup> k' \<^esup> s1" and
         "(encode_tape_instr L,s1) \<Rightarrow>\<^bsup> k'' \<^esup> s" and
         "k'' = 8" using encode_L by fastforce
  then have "s1 = s'" using big_step_t_determ2 encode_instr by blast
  also have "k' + k'' = k"
    by (meson Seq \<open>(c, s0) \<Rightarrow>\<^bsup> k' \<^esup> s1\<close> \<open>(encode_tape_instr L, s1) \<Rightarrow>\<^bsup> k'' \<^esup> s\<close> big_step_t_determ2 encode_L)
  from encode_L have "(c;;''y''::= (V ''y''\<lless>);;''t''::=(V ''x''\<doteq>1);;''y''::= ((V ''y'') \<oplus> (V ''t''));; ''x''::= (V ''x''\<then>),s0) \<Rightarrow>\<^bsup> k \<^esup> s" by fastforce
  have "(c;;''y''::= (V ''y''\<lless>);;''t''::=(V ''x''\<doteq>1);;''y''::= ((V ''y'') \<oplus> (V ''t''));; ''x''::= (V ''x''\<then>),s0) \<Rightarrow>\<^bsup> k \<^esup>  s1
    (''t'' := s1 ''x'' mod 2, ''y'' := LeftShift_nat (s1 ''y'') + s1 ''x'' mod 2,
     ''x'' := aval (V ''x''\<then>) (s1(''t'' := s1 ''x'' mod 2, ''y'' := LeftShift_nat (s1 ''y'') + s1 ''x'' mod 2)))"
    apply(rule Seq) apply(rule Seq) apply(rule Seq) apply(rule Seq) apply(auto) apply(fact) apply(rule AssignI) using \<open>k' + k'' = k\<close> \<open>k'' = 8\<close> by auto
  then show ?thesis
    by (smt (z3) \<open>(c;; ''y'' ::= V ''y''\<lless>;; ''t'' ::= (V ''x'' \<doteq>1);; ''y'' ::= (V ''y'' \<oplus> V ''t'');; ''x'' ::= (V ''x''\<then>), s0) \<Rightarrow>\<^bsup> k \<^esup> s\<close> \<open>s1 = s'\<close> atomVal.simps(1) aval.simps(5) big_step_t_determ2 char.inject fun_upd_other fun_upd_same list.inject)
qed

lemma encode_L_y: 
  assumes encode_L: "(c;;(encode_tape_instr L),s0) \<Rightarrow>\<^bsup> k \<^esup> s"
    and encode_instr: "(c,s0) \<Rightarrow>\<^bsup> k' \<^esup> s'"
  shows "s ''y'' = s' ''y'' * 2 + s' ''x'' mod 2"
  using assms proof -
  obtain k' s1 k'' where "(c,s0) \<Rightarrow>\<^bsup> k' \<^esup> s1" and
         "(encode_tape_instr L,s1) \<Rightarrow>\<^bsup> k'' \<^esup> s" and
         "k'' = 8" using encode_L by fastforce
  then have "s1 = s'" using big_step_t_determ2 encode_instr by blast
  have "k' + k'' = k"
    by (meson Seq \<open>(c, s0) \<Rightarrow>\<^bsup> k' \<^esup> s1\<close> \<open>(encode_tape_instr L, s1) \<Rightarrow>\<^bsup> k'' \<^esup> s\<close> big_step_t_determ2 encode_L)
  from encode_L have "(c;;''y''::= (V ''y''\<lless>);;''t''::=(V ''x''\<doteq>1);;''y''::= ((V ''y'') \<oplus> (V ''t''));; ''x''::= (V ''x''\<then>),s0) \<Rightarrow>\<^bsup> k \<^esup> s" by fastforce
  have "(c;;''y''::= (V ''y''\<lless>);;''t''::=(V ''x''\<doteq>1);;''y''::= ((V ''y'') \<oplus> (V ''t''));; ''x''::= (V ''x''\<then>),s0) \<Rightarrow>\<^bsup> k \<^esup>  s1
    (''t'' := s1 ''x'' mod 2, ''y'' := LeftShift_nat (s1 ''y'') + s1 ''x'' mod 2,
     ''x'' := aval (V ''x''\<then>) (s1(''t'' := s1 ''x'' mod 2, ''y'' := LeftShift_nat (s1 ''y'') + s1 ''x'' mod 2)))"
    apply(rule Seq) apply(rule Seq) apply(rule Seq) apply(rule Seq) apply(auto) apply(fact) apply(rule AssignI) using \<open>k' + k'' = k\<close> \<open>k'' = 8\<close> by auto
  then show ?thesis
    by (smt (z3) \<open>(c;; ''y'' ::= V ''y''\<lless>;; ''t'' ::= (V ''x'' \<doteq>1);; ''y'' ::= (V ''y'' \<oplus> V ''t'');; ''x'' ::= (V ''x''\<then>), s0) \<Rightarrow>\<^bsup> k \<^esup> s\<close> \<open>s1 = s'\<close> big_step_t_determ2 char.inject fun_upd_apply le_add1 list.inject mult_2_right)
qed

lemma update_encode_L:
  assumes encode_L: "((encode_tape_instr L),s0) \<Rightarrow>\<^bsup> k \<^esup> s"
  assumes update_L: "(l,r) = update L (l0,r0)"
  and tape_state_eq: "s0 ''x'' = tape_to_nat l0 \<and> s0 ''y'' = tape_to_nat r0"
shows "s ''x'' = tape_to_nat l" "s ''y'' = tape_to_nat r" 
proof -
  from encode_L encode_L_x have "s ''x'' = s0 ''x'' div 2" by auto
  then have "s ''x'' = tape_to_nat l0 div 2" using tape_state_eq by simp
  moreover have "l = tl l0" using update_L
    by (metis Nil_tl Turing.update.simps(3) prod.inject)
  moreover have "tape_to_nat (tl l0) = tape_to_nat l0 div 2" by (induct l0) auto
  ultimately show "s ''x'' = tape_to_nat l" by simp 
  next
    from encode_L encode_L_y have "s ''y'' = s0 ''y'' * 2 + s0 ''x'' mod 2" by blast
    then have "s ''y'' = tape_to_nat r0 * 2 + tape_to_nat l0 mod 2" using tape_state_eq by simp
    have "r = (if l0 = [] then (Bk#r0) else (hd l0 # r0))" using update_L by auto
    then have "tape_to_nat r =  tape_to_nat r0 * 2 + tape_to_nat l0 mod 2" proof (cases l0)
      case Nil
      then have "r = (Bk#r0)"
        by (simp add: \<open>r = (if l0 = [] then Bk # r0 else hd l0 # r0)\<close>)
      then show ?thesis using local.Nil by auto
    next
      case (Cons a list)
      then show ?thesis proof (cases a)
        case Bk
      then have "r = (Bk#r0)" by (simp add: \<open>r = (if l0 = [] then Bk # r0 else hd l0 # r0)\<close> local.Cons)
        then show ?thesis by (simp add: Bk local.Cons)
      next
        case Oc
        then have "r = (Oc#r0)" by (simp add: \<open>r = (if l0 = [] then Bk # r0 else hd l0 # r0)\<close> local.Cons)
        then have "tape_to_nat r =  tape_to_nat r0 * 2 + 1" by simp
        have "odd(tape_to_nat (Oc#list))" by simp
        then have "tape_to_nat (Oc#list) mod 2 = 1" by presburger
        show ?thesis
          using Oc \<open>tape_to_nat (Oc # list) mod 2 = 1\<close> \<open>tape_to_nat r = tape_to_nat r0 * 2 + 1\<close> local.Cons by auto
      qed
    qed
    then show "s ''y'' = tape_to_nat r" by (simp add: \<open>s ''y'' = tape_to_nat r0 * 2 + tape_to_nat l0 mod 2\<close>)
  qed

lemma encode_R_y: 
  assumes encode_R: "(c;;(encode_tape_instr R),s0) \<Rightarrow>\<^bsup> k \<^esup> s"
    and encode_instr: "(c,s0) \<Rightarrow>\<^bsup> k' \<^esup> s'"
shows "s ''y'' = s' ''y'' div 2"
  using assms proof -
  obtain k' s1 k'' where "(c,s0) \<Rightarrow>\<^bsup> k' \<^esup> s1" and
         "(encode_tape_instr R,s1) \<Rightarrow>\<^bsup> k'' \<^esup> s" and
         "k'' = 8" using encode_R by fastforce
  then have "s1 = s'" using big_step_t_determ2 encode_instr by blast
  have "k' + k'' = k"
    by (meson Seq \<open>(c, s0) \<Rightarrow>\<^bsup> k' \<^esup> s1\<close> \<open>(encode_tape_instr R, s1) \<Rightarrow>\<^bsup> k'' \<^esup> s\<close> big_step_t_determ2 encode_R)
  from encode_R have "(c;;''x''::= (V ''x''\<lless>);;''t''::=(V ''y''\<doteq>1);;''x''::= ((V ''x'') \<oplus> (V ''t''));;''y''::= (V ''y''\<then>),s0) \<Rightarrow>\<^bsup> k \<^esup> s" by fastforce
  have "(c;;''x''::= (V ''x''\<lless>);;''t''::=(V ''y''\<doteq>1);;''x''::= ((V ''x'') \<oplus> (V ''t''));;''y''::= (V ''y''\<then>),s0) \<Rightarrow>\<^bsup> k \<^esup> s1
    (''t'' := s1 ''y'' mod 2, ''x'' := LeftShift_nat (s1 ''x'') + s1 ''y'' mod 2,
     ''y'' := aval (V ''y''\<then>) (s1(''t'' := s1 ''y'' mod 2, ''x'' := LeftShift_nat (s1 ''x'') + s1 ''y'' mod 2)))"
    apply(rule Seq) apply(rule Seq) apply(rule Seq) apply(rule Seq) apply(auto) apply(fact) apply(rule AssignI) using \<open>k' + k'' = k\<close> \<open>k'' = 8\<close> by auto
  then show ?thesis
    by (smt (z3) \<open>(c;; ''x'' ::= V ''x''\<lless>;; ''t'' ::= (V ''y'' \<doteq>1);; ''x'' ::= (V ''x'' \<oplus> V ''t'');; ''y'' ::= (V ''y''\<then>), s0) \<Rightarrow>\<^bsup> k \<^esup> s\<close> \<open>s1 = s'\<close> atomVal.simps(1) aval.simps(5) big_step_t_determ2 char.inject fun_upd_other fun_upd_same list.inject)
qed

lemma encode_R_x: 
  assumes encode_R: "(c;;(encode_tape_instr R),s0) \<Rightarrow>\<^bsup> k \<^esup> s"
    and encode_instr: "(c,s0) \<Rightarrow>\<^bsup> k' \<^esup> s'"
shows "s ''x'' = s' ''x'' * 2 + s' ''y'' mod 2"
  using assms proof -
  obtain k' s1 k'' where "(c,s0) \<Rightarrow>\<^bsup> k' \<^esup> s1" and
         "(encode_tape_instr R,s1) \<Rightarrow>\<^bsup> k'' \<^esup> s" and
         "k'' = 8" using encode_R by fastforce
  then have "s1 = s'" using big_step_t_determ2 encode_instr by blast
  have "k' + k'' = k"
    by (meson Seq \<open>(c, s0) \<Rightarrow>\<^bsup> k' \<^esup> s1\<close> \<open>(encode_tape_instr R, s1) \<Rightarrow>\<^bsup> k'' \<^esup> s\<close> big_step_t_determ2 encode_R)
  from encode_R have "(c;;''x''::= (V ''x''\<lless>);;''t''::=(V ''y''\<doteq>1);;''x''::= ((V ''x'') \<oplus> (V ''t''));;''y''::= (V ''y''\<then>),s0) \<Rightarrow>\<^bsup> k \<^esup> s" by fastforce
  have "(c;;''x''::= (V ''x''\<lless>);;''t''::=(V ''y''\<doteq>1);;''x''::= ((V ''x'') \<oplus> (V ''t''));;''y''::= (V ''y''\<then>),s0) \<Rightarrow>\<^bsup> k \<^esup> s1
    (''t'' := s1 ''y'' mod 2, ''x'' := LeftShift_nat (s1 ''x'') + s1 ''y'' mod 2,
     ''y'' := aval (V ''y''\<then>) (s1(''t'' := s1 ''y'' mod 2, ''x'' := LeftShift_nat (s1 ''x'') + s1 ''y'' mod 2)))"
    apply(rule Seq) apply(rule Seq) apply(rule Seq) apply(rule Seq) apply(auto) apply(fact) apply(rule AssignI) using \<open>k' + k'' = k\<close> \<open>k'' = 8\<close> by auto
  then show ?thesis
      by (smt (z3) \<open>(c;;''x''::= (V ''x''\<lless>);;''t''::=(V ''y''\<doteq>1);;''x''::= ((V ''x'') \<oplus> (V ''t''));;''y''::= (V ''y''\<then>),s0) \<Rightarrow>\<^bsup> k \<^esup> s\<close> \<open>s1 = s'\<close> big_step_t_determ2 char.inject fun_upd_apply le_add1 list.inject mult_2_right)
qed

lemma update_encode_R:
  assumes encode_R: "((encode_tape_instr R),s0) \<Rightarrow>\<^bsup> k \<^esup> s"
  assumes update_R: "(l,r) = update R (l0,r0)"
  and tape_state_eq: "s0 ''x'' = tape_to_nat l0 \<and> s0 ''y'' = tape_to_nat r0"
shows "s ''x'' = tape_to_nat l " "s ''y'' = tape_to_nat r" 
proof -
  from encode_R encode_R_y have "s ''y'' = s0 ''y'' div 2" by auto
  then have "s ''y'' = tape_to_nat r0 div 2" using tape_state_eq by simp
  moreover have "r = tl r0" using update_R
    by (metis Nil_tl Turing.update.simps(4) prod.inject)
  moreover have "tape_to_nat (tl r0) = tape_to_nat r0 div 2" by (induct r0) auto
  ultimately show "s ''y'' = tape_to_nat r" by simp 
  next
    from encode_R encode_R_x have "s ''x'' = s0 ''x'' * 2 + s0 ''y'' mod 2" by blast
    then have "s ''x'' = tape_to_nat l0 * 2 + tape_to_nat r0 mod 2" using tape_state_eq by simp
    have "l = (if r0 = [] then (Bk#l0) else (hd r0 # l0))" using update_R by auto
    then have "tape_to_nat l =  tape_to_nat l0 * 2 + tape_to_nat r0 mod 2" proof (cases r0)
      case Nil
      then have "l = (Bk#l0)"
        by (simp add: \<open>l = (if r0 = [] then (Bk#l0) else (hd r0 # l0))\<close>)
      then show ?thesis using local.Nil by auto
    next
      case (Cons a list)
      then show ?thesis proof (cases a)
        case Bk
      then have "l = (Bk#l0)" by (simp add: \<open>l = (if r0 = [] then (Bk#l0) else (hd r0 # l0))\<close> local.Cons)
        then show ?thesis by (simp add: Bk local.Cons)
      next
        case Oc
        then have "l = (Oc#l0)" by (simp add: \<open>l = (if r0 = [] then (Bk#l0) else (hd r0 # l0))\<close> local.Cons)
        then have "tape_to_nat l =  tape_to_nat l0 * 2 + 1" by simp
        have "odd(tape_to_nat (Oc#list))" by simp
        then have "tape_to_nat (Oc#list) mod 2 = 1" by presburger
        show ?thesis
          using Oc \<open>tape_to_nat (Oc # list) mod 2 = 1\<close> \<open>tape_to_nat l =  tape_to_nat l0 * 2 + 1\<close> local.Cons by auto
      qed
    qed
    then show "s ''x'' = tape_to_nat l" by (simp add: \<open>s ''x'' = tape_to_nat l0 * 2 + tape_to_nat r0 mod 2\<close>)
  qed



subsection "Transforming Turing Machine to IMP-"

abbreviation nth_name:: "nat \<Rightarrow> string" where
"nth_name n \<equiv> (as_string ((next^^n) (default::name)))"


text "After each iteration exactly one variable of the set corresponding to the states of the turing machine is 0.
We step into that statement and read the current head and store it in t and then step into the corresponding statement and 
encode the turing machine operation as an arithmetic one."
fun turing_to_while_acc :: "tprog0 \<Rightarrow> name \<Rightarrow> com" where (* state has to evaluate all variables to 1 except (next (default::name)) which has to be 0 at the beginning *)
"turing_to_while_acc [] _ = SKIP" |
"turing_to_while_acc ((a0,s0)#(a1,s1)#is) n = turing_to_while_acc is (next n);;
  IF (as_string n)\<noteq>0 THEN SKIP
                     ELSE (''t''::=(V ''x''\<doteq>1);;IF ''t''\<noteq>0 THEN   
                            encode_tape_instr a1;;(nth_name s1)::=A (N 0);;(as_string n)::=A (N 1);;''z''::=(A(N s1))
                          ELSE encode_tape_instr a0;;(nth_name s0)::=A (N 0);;(as_string n)::=A (N 1));;''z''::=(A(N s0))"
text "We iterate through the while loop until we enter the halting state/accepting state which corresponds to default:name (_)."
fun turing_to_while :: "config \<Rightarrow> tprog0 \<Rightarrow> com" where
"turing_to_while c p = (let (z,x,y) = encode_tape c in (''z''::=A (N z);;''x''::=A (N x);;''y''::=A (N y)));;
                                          WHILE (as_string (default::name))\<noteq>0 DO turing_to_while_acc p (next default)"

lemma conversion_correct_current_state:
  assumes "(turing_to_while_acc p n, \<lambda>s. if s=''x'' then tape_to_nat l else if s=''y'' then tape_to_nat r else if s = nth_name state then 0 else 1) \<Rightarrow>\<^bsup> k \<^esup> s" 
  and "encode_tape (step0 (state,l,r) p) = (s1,l1,r1)"
  and is_in_program: "nth_name state \<in> set (Max_Constant.all_variables (turing_to_while_acc p n))"
  and tm_wf: "tm_wf0 p"
shows "(s1,l1,r1) = (s ''z'', s ''x'', s ''y'')"
  using assms proof(induction p n rule: turing_to_while_acc.induct)
    case (1 uu)
    then show ?case by simp
  next
    case (2 a0 s0 a1 s1 "is" n)          
    from is_in_program have "nth_name state \<in> set (all_variables (turing_to_while_acc ((a0, s0) # (a1, s1) # is) n))"
      using "2.prems"(3) by blast
    then consider "nth_name state \<in> set (all_variables (turing_to_while_acc is (next n)))" | 
    "nth_name state \<in> set (all_variables (turing_to_while_acc ((a0, s0) # [(a1, s1)]) n))" by auto
      then show ?case sorry
  next
    case (3 v b)
    then show ?case by simp
  qed

lemma state_contained:
  assumes tm_wf: "tm_wf0 p"
  and "nth_name e = as_string n" "e > 1"
  and is_valid_state: "2 * s \<le> length p" "s > 0"(* s > 0 cause 0 is special halting case, treated in the while loop and 2 * s \<le> length p cause there are at most p div 2 states *)
shows "nth_name s \<in> set (Max_Constant.all_variables (turing_to_while_acc p n))"
  using assms proof(induction p n rule: turing_to_while_acc.induct)
  case (1 uu)
  then show ?case by simp
next
  case (2 a0 s0 a1 s1 "is" n)
  then show ?case sorry
next
  case (3 v b)
  then show ?case by simp
qed


lemma conversion_step_correct:
  assumes tm_wf: "tm_wf0 p"
  and "(turing_to_while_acc p n, \<lambda>s. if s=''x'' then tape_to_nat l else if s=''y'' then tape_to_nat r else if s = nth_name state then 0 else 1) \<Rightarrow>\<^bsup> k \<^esup> s" 
  and "encode_tape (step0 (state,l,r) p) = (s1,l1,r1)"
  shows "(s1,l1,r1) = (s ''z'', s ''x'', s ''y'')"
  using assms proof(induction p n rule: turing_to_while_acc.induct)
    case (1 uu)
    then show ?case by simp
  next
    case (2 a0 s0 a1 s1 "is" n)          
    then show ?case sorry
  next
    case (3 v b)
    then show ?case by simp
  qed

lemma conversion_correct:
  assumes tm_wf: "tm_wf (p,0)"
  and tm_accepts: "is_final(steps0 c p n)"
  and "(turing_to_while c p, \<lambda>s. if s = ''__'' then 0 else 1) \<Rightarrow>\<^bsup> k \<^esup> s " 
  shows "encode_tape (steps0 c p n) = (s ''_'',s ''x'', s ''y'')"
  using assms proof (induct p)
      case Nil
      then show ?case using tm_wf by force
    next
      case (Cons a p)
      then show ?case sorry
    qed