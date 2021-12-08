theory turing_to_while
  imports Main "Turing" "../IMP-/Com" "../IMP-/Big_StepT" "../IMP-/Small_StepT" "../IMP-/Big_Step_Small_Step_Equivalence" "../fresh_names/Fresh_Class"

begin

type_synonym enc_tape = "nat \<times> nat \<times> nat"
abbreviation LeftShift_nat:: "nat \<Rightarrow> nat" where
" LeftShift_nat a \<equiv> a + a"

fun encode_tape_acc :: "config \<Rightarrow> enc_tape \<Rightarrow> enc_tape" where
"encode_tape_acc (s,[],[]) (z,x,y) = (s,x,y)" |
"encode_tape_acc (s,[],r#rs) (z,x,y) = (if r = Bk then (encode_tape_acc (s,[],rs) (z,x,LeftShift_nat y)) 
                                                  else (encode_tape_acc (s,[],rs) (z,x,(LeftShift_nat y) + 1)))" |
"encode_tape_acc (s,l#ls,r) (z,x,y) = (if l = Bk then (encode_tape_acc (s,ls,r) (z,LeftShift_nat x,y)) else (encode_tape_acc (s,ls,r) (z, (LeftShift_nat x) + 1,y)))"

fun encode_tape :: "config \<Rightarrow> enc_tape" where
"encode_tape (s,ls,rs) = encode_tape_acc (s,ls, rev rs) (0,0,0)"

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


fun turing_to_while :: "config \<Rightarrow> tprog0 \<Rightarrow> name \<Rightarrow> com" where
"turing_to_while c [] _ = (let (z,x,y) = encode_tape c in (''z''::=A (N z);;''x''::=A (N x);;''y''::=A (N y)));;WHILE (as_string (default::name))\<noteq>0 DO SKIP" |
"turing_to_while c ((a0,s0)#(a1,s1)#is) n = turing_to_while c is (next n);;IF (as_string n)\<noteq>0 THEN 
                                                              (''t''::=(V ''x''\<doteq>1);;IF ''t''\<noteq>0 THEN 
                                                                      encode_tape_instr a1;;(nth_name s1)::=A (N 1);;(as_string n)::=A (N 0)
                                                                 ELSE encode_tape_instr a0;;(nth_name s0)::=A (N 1);;(as_string n)::=A (N 0)) 
                                                                           ELSE SKIP"

value "aval(RightShift (N 2)) <> "
value "as_string(next (next default::name))"
value "as_string ((next^^0) (default::name))"
value "(SKIP,<>)