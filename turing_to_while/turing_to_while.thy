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

fun is_cell_list_eq :: "cell list \<Rightarrow> cell list \<Rightarrow> bool" where (*proof correctness; how? probably via proofing equality on fetch command*)
"is_cell_list_eq xs ys = (dropWhile (\<lambda>x. x = Bk)(rev xs)  = dropWhile (\<lambda>y. y = Bk) (rev ys))"


lemma nat_to_tape_bk: "\<lbrakk>n > 0\<rbrakk> \<Longrightarrow> Bk # (nat_to_tape n) = nat_to_tape (2*n)"
  apply(induct n)
   apply(auto)
  done
lemma is_cell_list_eq_bk: "is_cell_list_eq (xs @ [Bk]) xs"
   apply(simp)
  done

lemma tape_to_nat_inverse: "tape_to_nat(nat_to_tape n) = n"
proof(induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case sorry
qed


lemma nat_to_tape_inverse: "is_cell_list_eq (nat_to_tape(tape_to_nat xs)) xs"
proof (induction xs rule: tape_to_nat.induct)
  case 1
  then show ?case by auto
next
  case (2 x xs)
  then show ?case
  proof (cases x)
    case Bk
    then have  "is_cell_list_eq (Bk # nat_to_tape (tape_to_nat xs)) (nat_to_tape (tape_to_nat xs))"
    then have "is_cell_list_eq (Bk # nat_to_tape (tape_to_nat xs)) (Bk#xs)"  sorry
  next
    case Oc
    then show ?thesis sorry
  qed
qed


lemma tape_to_nat_inverse: "tape_to_nat(nat_to_tape n) = n"
  sorry

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

lemma conversion_step_correct: 
  assumes tm_wf: "tm_wf (p,1)"
  and tm_accepts: "is_final(steps c (p,1) n)"
  and "(turing_to_while c p (next default), \<lambda>s. if s = ''__'' then 0 else 1) \<Rightarrow>\<^bsup> k \<^esup> s " 
  shows "encode_tape (steps c (p,1) n) = (s ''_'',s ''x'', s ''y'')"

lemma conversion_correct:
  assumes tm_wf: "tm_wf (p,1)"
  and tm_accepts: "is_final(steps c (p,1) n)"
  and "(turing_to_while c p (next default), \<lambda>s. if s = ''__'' then 0 else 1) \<Rightarrow>\<^bsup> k \<^esup> s " 
  shows "encode_tape (steps c (p,1) n) = (s ''_'',s ''x'', s ''y'')"
  using assms proof (induct p)
      case Nil
      then show ?case using tm_wf by force
    next
      case (Cons a p)
      then show ?case sorry
    qed