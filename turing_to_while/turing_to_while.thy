theory turing_to_while
  imports Main "Turing" "../IMP-/Com" "../IMP-/Big_StepT" "../IMP-/Small_StepT" "../IMP-/Big_Step_Small_Step_Equivalence" "../fresh_names/Fresh_Class" "../IMP-/Max_Constant"

begin

subsection "Transformation of the Tape to Natural Numbers and Back"
type_synonym enc_tape = "nat \<times> nat \<times> nat"
abbreviation LeftShift_nat:: "nat \<Rightarrow> nat" where
" LeftShift_nat a \<equiv> a + a"

fun tape_to_nat :: "cell list \<Rightarrow> nat" where
"tape_to_nat [] = 0" |
"tape_to_nat (x#xs) = (if x = Bk then LeftShift_nat (tape_to_nat xs)
                                   else LeftShift_nat (tape_to_nat xs) + 1)"

lemma t2n_0: "(\<forall>x\<in> set xs. x = Bk) \<longleftrightarrow>  tape_to_nat xs = 0 "
  apply(induct xs)
   apply(auto)
  done

fun encode_tape :: "config \<Rightarrow> enc_tape" where
"encode_tape (s,ls,rs) = (s, tape_to_nat ls, tape_to_nat rs)"

value "encode_tape (42, [Oc, Bk, Oc, Oc], [Oc, Bk, Oc, Oc])"

fun nat_to_tape :: "nat \<Rightarrow> cell list" where
"nat_to_tape 0 = []" |
"nat_to_tape n = (if (n mod 2) = 1 then Oc else Bk) # nat_to_tape (n div 2)"


lemma nat_to_tape_double[simp]: "n > 0 \<Longrightarrow> nat_to_tape (2 * n) = Bk # (nat_to_tape n)"
  apply(induct n)
   apply(auto)
  done

lemma nat_to_tape_nth_bit: "nat_to_tape (2^n) = replicate n Bk  @ [Oc]"
  apply(induct n)
   apply(auto)
  done

fun decode_tape :: "enc_tape \<Rightarrow> config" where
"decode_tape (z,n,m) = (z, nat_to_tape n, nat_to_tape m)"
value "nat_to_tape(13)"
value "tape_to_nat([Oc,Bk,Oc,Oc])"
value "tape_to_nat([Bk,Bk,Bk,Bk,Oc,Bk,Bk])"
value "nat_to_tape(tape_to_nat([Bk,Oc]))"
value "tape_to_nat([Oc])"

fun is_cell_list_eq :: "cell list \<Rightarrow> cell list \<Rightarrow> bool" where (*proof correctness; how? probably via proofing equality on fetch command*)
"is_cell_list_eq xs ys = (dropWhile (\<lambda>x. x = Bk)(rev xs)  = dropWhile (\<lambda>y. y = Bk) (rev ys))"


lemma tape_to_nat_app_bk[simp]: "tape_to_nat (xs @ [Bk]) = tape_to_nat xs"
  apply(induct xs)
   apply(auto)
  done

lemma is_cell_list_eq_same[simp]: "is_cell_list_eq xs xs"
  apply(induct xs)
   apply(auto)
  done

lemma is_cell_list_eq_cons:
  assumes "is_cell_list_eq xs ys"
  shows "is_cell_list_eq (x#xs) (x#ys)"
using assms proof -
  have "(dropWhile (\<lambda>x. x = Bk)(rev xs) = dropWhile (\<lambda>y. y = Bk) (rev ys))" using assms by auto
  then have "(if (\<forall>x\<in>set xs.  x = Bk) then dropWhile(\<lambda>x. x = Bk) [] else dropWhile (\<lambda>x. x = Bk) (rev xs) @ []) = 
            (if (\<forall>x\<in>set ys.  x = Bk) then dropWhile(\<lambda>x. x = Bk) [] else dropWhile (\<lambda>x. x = Bk) (rev ys) @ [])" 
    by (smt (verit, best) dropWhile_eq_Nil_conv set_rev)
  then have "(if (\<forall>x\<in>set xs.  x = Bk) then dropWhile(\<lambda>x. x = Bk) [x] else dropWhile (\<lambda>x. x = Bk) (rev xs) @ [x]) = 
            (if (\<forall>x\<in>set ys.  x = Bk) then dropWhile(\<lambda>x. x = Bk) [x] else dropWhile (\<lambda>x. x = Bk) (rev ys) @ [x])"
    by (smt (verit, best) \<open>dropWhile (\<lambda>x. x = Bk) (rev xs) = dropWhile (\<lambda>y. y = Bk) (rev ys)\<close> dropWhile_eq_Nil_conv set_rev)
  then have "(dropWhile (\<lambda>x. x = Bk)((rev xs) @ [x]) = dropWhile (\<lambda>y. y = Bk) ((rev ys) @ [x]))" by (simp add: dropWhile_append)
  then show ?thesis by simp
qed


lemma tape_to_nat_inverse: "tape_to_nat(nat_to_tape n) = n"
proof(induct n rule: nat_to_tape.induct)
  case 1
  then show ?case by simp
next
  case (2 v)
  then show ?case
    proof (cases v rule: parity_cases)
    case even
    then have "tape_to_nat (nat_to_tape (Suc v)) = tape_to_nat (Oc # nat_to_tape (Suc v div 2))" by auto
    also have "... = 2 * tape_to_nat(nat_to_tape (Suc v div 2)) + 1" by simp
    also have "... = 2 * (Suc v div 2) + 1" using "2" by simp
    then show ?thesis by (metis calculation even(1) even_Suc odd_two_times_div_two_succ)
  next
    case odd
    then have "tape_to_nat (nat_to_tape (Suc v)) = tape_to_nat (Bk # nat_to_tape (Suc v div 2))" by simp
    also have "... = 2 * tape_to_nat (nat_to_tape (Suc v div 2))" by simp
    also have "... = 2 * Suc v div 2" by (metis "2" div_mult_swap even_Suc odd(1))
    finally show ?thesis by auto
        qed
qed

lemma nat_to_tape_inverse: "is_cell_list_eq (nat_to_tape(tape_to_nat xs)) xs"
proof (induction xs rule: tape_to_nat.induct)
  case 1
  then show ?case by simp
next
  case (2 x xs)
  then show ?case proof (cases x)
    case Bk
    then have "is_cell_list_eq (nat_to_tape(tape_to_nat xs)) xs" using 2 by simp
    then have Bk_cons: "is_cell_list_eq (Bk # nat_to_tape(tape_to_nat xs)) (Bk#xs)" using is_cell_list_eq_cons by fast
    consider "(\<forall>x\<in>set xs. x = Bk)" | "Oc \<in> set xs" using cell.exhaust by auto
    then have "is_cell_list_eq (nat_to_tape(2 * tape_to_nat xs)) (Bk#xs)" proof (cases)
      case 1
       then show ?thesis using t2n_0 Bk_cons by simp
    next
      case 2
      then show ?thesis using Bk_cons using t2n_0 by fastforce
    qed (* case distinction on xs all blank vs some Oc *)
    then show ?thesis by (simp add: Bk mult_2)
  next
    case Oc
    then have "is_cell_list_eq (nat_to_tape(tape_to_nat xs)) xs" using 2 by simp
    then have "is_cell_list_eq (Oc # nat_to_tape(tape_to_nat xs)) (Oc#xs)" using is_cell_list_eq_cons by fast
    then have "is_cell_list_eq (nat_to_tape(2 * tape_to_nat xs + 1)) (Oc#xs)" by simp
    then show ?thesis by (simp add: Oc mult_2)
  qed
qed


lemma encode_decode_inverse: "(z,x,y) = encode_tape(decode_tape(z,x,y))"
  sorry



subsection "Encoding of Tape Instructions As arithmetic Operations"

abbreviation LeftShift:: "atomExp \<Rightarrow> aexp" ("_\<lless>") where
"LeftShift a \<equiv> Plus a a"

fun encode_tape_instr :: "action  \<Rightarrow> com" where
"encode_tape_instr a = (case a of Nop \<Rightarrow> SKIP |
                                  W0 \<Rightarrow> ''y''::= (V ''y''\<then>);;''y''::= (V ''y''\<lless>) |
                                  W1 \<Rightarrow> ''y''::= (V ''y''\<then>);;''y''::=(V ''y''\<lless>);;''y''::= ((V ''y'') \<oplus> (N 1)) |
                                  L \<Rightarrow> ''y''::= (V ''y''\<lless>);;''t''::=(V ''x''\<doteq>1);;''y''::= ((V ''y'') \<oplus> (V ''t''));; ''x''::= (V ''x''\<then>) |
                                  R \<Rightarrow> ''x''::= (V ''x''\<lless>);;''t''::=(V ''y''\<doteq>1);;''x''::= ((V ''x'') \<oplus> (V ''t''));;''y''::= (V ''y''\<then>))"

lemma rightShift_state: 
  assumes rightShift_com: "(v::= (V v\<then>), s) \<Rightarrow>\<^bsup> k \<^esup> s'"
  shows " s(v := s v div 2) = s'" 
  using assms proof -
   show ?thesis using rightShift_com by auto
 qed

lemma rightShift_state_: 
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


lemma encode_L_x: 
  assumes encode_L: "(c;;(encode_tape_instr L),s0) \<Rightarrow>\<^bsup> k \<^esup> s"
    and encode_instr: "(c,s0) \<Rightarrow>\<^bsup> k' \<^esup> s'"
shows "s ''x'' = s' ''x'' div 2"
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

lemma encode_R_x: 
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

lemma encode_R_y: 
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




subsection "Transforming Turing Machine to IMP-"

abbreviation nth_name:: "nat \<Rightarrow> string" where
"nth_name n \<equiv> (as_string ((next^^n) (default::name)))"


fun turing_to_while_acc :: "tprog0 \<Rightarrow> name \<Rightarrow> com" where (* state has to evaluate all variables to 1 except (next (default::name)) which has to be 0 at the beginning *)
"turing_to_while_acc [] _ = SKIP" |
"turing_to_while_acc ((a0,s0)#(a1,s1)#is) n = turing_to_while_acc is (next n);;
  IF (as_string n)\<noteq>0 THEN SKIP
                     ELSE (''t''::=(V ''x''\<doteq>1);;IF ''t''\<noteq>0 THEN 
                            encode_tape_instr a1;;(nth_name s1)::=A (N 0);;(as_string n)::=A (N 1);;''z''::=(A(N s1))
                          ELSE encode_tape_instr a0;;(nth_name s0)::=A (N 0);;(as_string n)::=A (N 1));;''z''::=(A(N s0)) "

fun turing_to_while :: "config \<Rightarrow> tprog0 \<Rightarrow> com" where
"turing_to_while c p = (let (z,x,y) = encode_tape c in (''z''::=A (N z);;''x''::=A (N x);;''y''::=A (N y)));;
                                          WHILE (as_string (default::name))\<noteq>0 DO turing_to_while_acc p (next default)"

lemma update_state_nop[simp]: 
  assumes tm_conversion: "(turing_to_while (q,l,r) p,\<lambda>s. if s = nth_name q then 0 else 1) \<Rightarrow>\<^bsup> k \<^esup> s"
    and tm_nop_conversion: "(turing_to_while (q,update Nop (l,r)) p,\<lambda>s. if s = nth_name q then 0 else 1) \<Rightarrow>\<^bsup> k \<^esup> s'"
  shows "s = s'"
proof -
  from tm_conversion have "(turing_to_while (q,l,r) p,\<lambda>s. if s = nth_name q then 0 else 1) \<Rightarrow>\<^bsup> k \<^esup> s" by simp
  then have "(turing_to_while (q,update Nop (l,r)) p,\<lambda>s. if s = nth_name q then 0 else 1) \<Rightarrow>\<^bsup> k \<^esup> s" by simp
  thus ?thesis using bigstep_det tm_nop_conversion by auto
qed

lemma conversion_step_correct: 
  assumes tm_wf: "tm_wf (p,1)"
  and "(turing_to_while_acc p (default::name), \<lambda>s. if s=''x'' then tape_to_nat l else if s=''y'' then tape_to_nat r else if s = nth_name state then 0 else 1) \<Rightarrow>\<^bsup> k \<^esup> s " 
  and "encode_tape (step0 (state,l,r) p) = (s1,l1,r1)"
  shows "(s1,l1,r1) = (s ''z'', s ''x'', s ''y'')"
  sorry
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