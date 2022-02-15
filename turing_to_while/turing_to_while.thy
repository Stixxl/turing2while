theory turing_to_while
  imports Main "Turing" "../IMP-/Com" "../IMP-/Big_StepT" "../IMP-/Small_StepT" "../IMP-/Big_Step_Small_Step_Equivalence" "../fresh_names/Fresh_Class"

begin

type_synonym enc_tape = "nat \<times> nat \<times> nat"
abbreviation LeftShift_nat:: "nat \<Rightarrow> nat" where
" LeftShift_nat a \<equiv> a + a"

fun tape_to_nat :: "cell list \<Rightarrow> nat" where
"tape_to_nat [] = 0" |
"tape_to_nat (x#xs) = (if x = Bk then LeftShift_nat (tape_to_nat xs)
                                   else LeftShift_nat (tape_to_nat xs) + 1)"

fun encode_tape :: "config \<Rightarrow> enc_tape" where
"encode_tape (s,ls,rs) = (s, tape_to_nat ls, tape_to_nat rs)"

value "encode_tape (42, [Oc, Bk, Oc, Oc], [Oc, Bk, Oc, Oc])"

fun nat_to_tape :: "nat \<Rightarrow> cell list" where
"nat_to_tape 0 = []" |
"nat_to_tape n = (if (n mod 2) = 1 then Oc else Bk) # nat_to_tape (n div 2)"

fun decode_tape :: "enc_tape \<Rightarrow> config" where
"decode_tape (z,n,m) = (z, nat_to_tape n, nat_to_tape m)"
value "nat_to_tape(13)"
value "tape_to_nat([Oc,Bk,Oc,Oc])"
value "tape_to_nat([Bk,Bk,Bk,Bk,Oc,Bk,Bk])"
value "nat_to_tape(tape_to_nat([Bk,Oc]))"

fun is_cell_list_eq :: "cell list \<Rightarrow> cell list \<Rightarrow> bool" where (*proof correctness; how? probably via proofing equality on fetch command*)
"is_cell_list_eq xs ys = (dropWhile (\<lambda>x. x = Bk)(rev xs)  = dropWhile (\<lambda>y. y = Bk) (rev ys))"


lemma tape_to_nat_app_bk[simp]: "tape_to_nat (xs @ [Bk]) = tape_to_nat xs"
  apply(induct xs)
   apply(auto)
  done

lemma tape_to_nat_elim_bk[simp]: "tape_to_nat(Bk#xs) = 2 * tape_to_nat xs"
  by simp

lemma is_cell_list_eq_same[simp]: "is_cell_list_eq xs xs"
  apply(induct xs)
   apply(auto)
  done

lemma tape_to_nat_inverse: "tape_to_nat(nat_to_tape n) = n"
proof(induct n rule: nat_to_tape.induct)
  case 1
  then show ?case by simp
next
  case (2 v)
  then show ?case sorry
qed

lemma tape_to_nat_app_occ: "tape_to_nat (xs @ [Oc]) = 2 ^ (length xs) + tape_to_nat xs"
  sorry

lemma nat_to_tape_app_occ: "2 ^ (length xs) + tape_to_nat xs"

lemma is_cell_list_eq_app_occ[simp]: "is_cell_list_eq (xy @ [Oc]) (xs @ [Oc]) \<longleftrightarrow> (xy @ [Oc]) = (xs @ [Oc])"
  by simp

lemma nat_to_tape_inverse: "is_cell_list_eq (nat_to_tape(tape_to_nat xs)) xs"
proof (induction xs rule: rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc x xs)
  then show ?case
  proof(cases x)
    case Bk
    from "snoc.IH" have "is_cell_list_eq (nat_to_tape (tape_to_nat xs)) (xs @ [Bk])" by simp
    then have "is_cell_list_eq (nat_to_tape (tape_to_nat xs) @ [Bk]) (xs @ [Bk])" by simp
    then have "is_cell_list_eq (nat_to_tape (tape_to_nat (xs @ [Bk]))) (xs @ [Bk])" by simp
    thus ?thesis by (simp add: Bk)
  next
    case Oc
    from "snoc.IH" have "is_cell_list_eq (nat_to_tape (tape_to_nat (xs @ [Oc]))) (xs @ [Oc])"
    then show ?thesis sorry

  qed
qed
lemma encode_decode_inverse: "(z,x,y) = encode_tape(decode_tape(z,x,y))"
  sorry

definition LeftShift:: "atomExp \<Rightarrow> aexp" ("_\<lless>") where
"LeftShift a = Plus a a"
definition encode_tape_instr :: "action  \<Rightarrow> com" where
"encode_tape_instr a = (case a of Nop \<Rightarrow> SKIP |
                                  W0 \<Rightarrow> ''y''::= (V ''y''\<then>);;''y''::= (V ''y''\<lless>) |
                                  W1 \<Rightarrow> ''y''::= (V ''y''\<then>);;''y''::=(V ''y''\<lless>);;''y''::= ((V ''y'') \<oplus> (N 1)) |
                                  L \<Rightarrow> ''y''::= (V ''y''\<lless>);;''t''::=(V ''x''\<doteq>1);;''y''::= ((V ''y'') \<oplus> (V ''t''));; ''x''::= (V ''x''\<then>) |
                                  R \<Rightarrow>''x''::= (V ''x''\<lless>);;''t''::=(V ''y''\<doteq>1);;''x''::= ((V ''x'') \<oplus> (V ''t''));;''y''::= (V ''y''\<then>))"

abbreviation nth_name:: "nat \<Rightarrow> string" where
"nth_name n \<equiv> (as_string ((next^^n) (default::name)))"


fun turing_to_while :: "config \<Rightarrow> tprog0 \<Rightarrow> name \<Rightarrow> com" where (* state has to evaluate all variables to 1 except (next (default::name)) which has to be 0 at the beginning *)
"turing_to_while c [] _ = (let (z,x,y) = encode_tape c in (''z''::=A (N z);;''x''::=A (N x);;''y''::=A (N y)));;
                                          WHILE (as_string (default::name))\<noteq>0 DO SKIP" |
"turing_to_while c ((a0,s0)#(a1,s1)#is) n = turing_to_while c is (next n);;
  IF (as_string n)\<noteq>0 THEN SKIP
                     ELSE (''t''::=(V ''x''\<doteq>1);;IF ''t''\<noteq>0 THEN 
                            encode_tape_instr a1;;(nth_name s1)::=A (N 0);;(as_string n)::=A (N 1)
                          ELSE encode_tape_instr a0;;(nth_name s0)::=A (N 0);;(as_string n)::=A (N 1)) "



lemma update_passthrough_nop[simp]: "turing_to_while (s,update Nop (l,r)) p (next default) = turing_to_while (s,l,r) p (next default)"
  by simp
lemma update_state_nop[simp]: 
  assumes tm_conversion: "(turing_to_while (q,l,r) p (next default),\<lambda>s. if s = nth_name q then 0 else 1) \<Rightarrow>\<^bsup> k \<^esup> s"
    and tm_nop_conversion: "(turing_to_while (q,update Nop (l,r)) p (next default),\<lambda>s. if s = nth_name q then 0 else 1) \<Rightarrow>\<^bsup> k \<^esup> s'"
  shows "s = s'"
proof -
  from tm_conversion have "(turing_to_while (q,l,r) p (next default),\<lambda>s. if s = nth_name q then 0 else 1) \<Rightarrow>\<^bsup> k \<^esup> s" by simp
  then have "(turing_to_while (q,update Nop (l,r)) p (next default),\<lambda>s. if s = nth_name q then 0 else 1) \<Rightarrow>\<^bsup> k \<^esup> s" by simp
  thus ?thesis using bigstep_det tm_nop_conversion by auto
qed
lemma update_passthrough_w0[simp]: "turing_to_while (s,update W0 (l,r)) p (next default) = turing_to_while (s,l,Bk#(tl r)) p (next default)"
  by simp
lemma update_state_w0[simp]: 
  assumes tm_conversion: "(turing_to_while (q,l,r) p (next default),\<lambda>s. if s = nth_name q then 0 else 1) \<Rightarrow>\<^bsup> k \<^esup> s"
    and tm_nop_conversion: "(turing_to_while (q,update W0 (l,r)) p (next default),\<lambda>s. if s = nth_name q then 0 else 1) \<Rightarrow>\<^bsup> k' \<^esup> s'"
  shows "s ''z'' = s' ''z''" (* \<and> s ''x'' = s' ''x'' \<and> s ''y'' \<ge> s' ''y''" *)
proof(induct "q l r p" rule: turing_to_while.induct)
qed
lemma update_passthrough_w1[simp]: "turing_to_while (s,update W1 (l,r)) p (next default) = turing_to_while (s,l,Oc#(tl r)) p (next default)"
  by simp
lemma update_passthrough_L[simp]: "turing_to_while (s,update L (l,r)) p (next default) = turing_to_while (s,tl l,if l=[] then Bk# r else (hd l)#r) p (next default)"
  by simp
lemma update_passthrough_R[simp]: "turing_to_while (s,update R (l,r)) p (next default) = turing_to_while (s,if r=[] then Bk# l else (hd r)#l, tl r) p (next default)"
  by simp


lemma conversion_step_correct: 
  assumes tm_wf: "tm_wf (p,1)"
  and "(turing_to_while (state,l,r) p (next default), \<lambda>s. if s = nth_name state then 0 else 1) \<Rightarrow>\<^bsup> k \<^esup> s " 
  and "encode_tape (step0 c p) = (s1,l1,r1)"
  shows "(l1,r1) = (s ''x'', s ''y'') \<and> s (nth_name state) = 0"
  sorry
lemma conversion_correct:
  assumes tm_wf: "tm_wf (p,0)"
  and tm_accepts: "is_final(steps0 c p n)"
  and "(turing_to_while c p (next default), \<lambda>s. if s = ''__'' then 0 else 1) \<Rightarrow>\<^bsup> k \<^esup> s " 
  shows "encode_tape (steps0 c p n) = (s ''_'',s ''x'', s ''y'')"
  using assms proof (induct p)
      case Nil
      then show ?case using tm_wf by force
    next
      case (Cons a p)
      then show ?case sorry
    qed