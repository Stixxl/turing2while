theory tape_nat_conversion
  imports Main "Turing" "../IMP-/Com" "../IMP-/Big_StepT" "../IMP-/Small_StepT" "../IMP-/Big_Step_Small_Step_Equivalence"  "../IMP-/Max_Constant"
begin

text "In this theory we prove the conversion between natural numbers and the tape as described in turing.thy . 
Note that this closely mirrors the conversion between a binary (in string format or similar) and natural numbers"
type_synonym enc_tape = "nat \<times> nat \<times> nat"
abbreviation LeftShift_nat:: "nat \<Rightarrow> nat" where
" LeftShift_nat a \<equiv> a + a"

subsection "Conversion from tape to natural"
fun tape_to_nat :: "cell list \<Rightarrow> nat" where
"tape_to_nat [] = 0" |                
"tape_to_nat (x#xs) = (if x = Bk then LeftShift_nat (tape_to_nat xs)
                                   else LeftShift_nat (tape_to_nat xs) + 1)"

fun encode_tape :: "config \<Rightarrow> enc_tape" where
"encode_tape (s,ls,rs) = (s, tape_to_nat ls, tape_to_nat rs)"

lemma t2n_0: "(\<forall>x\<in> set xs. x = Bk) \<longleftrightarrow>  tape_to_nat xs = 0 "
  apply(induct xs)
   apply(auto)
  done

lemma tape_to_nat_even: "even (tape_to_nat xs) \<longleftrightarrow> hd xs = Bk \<or> xs = []"
  apply (induct xs)
   apply(auto)
  done

lemma tape_to_nat_odd: " xs \<noteq> [] \<Longrightarrow> odd (tape_to_nat xs) \<longleftrightarrow> hd xs = Oc"
  apply (induct xs)
  using cell.exhaust by auto

subsection "Conversion from natural to tape"
fun nat_to_tape :: "nat \<Rightarrow> cell list" where
"nat_to_tape 0 = []" |
"nat_to_tape n = (if (n mod 2) = 1 then Oc else Bk) # nat_to_tape (n div 2)"


fun decode_tape :: "enc_tape \<Rightarrow> config" where
"decode_tape (z,n,m) = (z, nat_to_tape n, nat_to_tape m)"

lemma nat_to_tape_double[simp]: "n > 0 \<Longrightarrow> nat_to_tape (2 * n) = Bk # (nat_to_tape n)"
  apply(induct n)
   apply(auto)
  done

lemma nat_to_tape_nth_bit: "nat_to_tape (2^n) = replicate n Bk  @ [Oc]"
  apply(induct n)
   apply(auto)
  done


text "This function is used to compare tapes with each other. Two tapes are considered equal, 
if they are the same ignoring any leading blank cells."
fun is_cell_list_eq :: "cell list \<Rightarrow> cell list \<Rightarrow> bool" where 
"is_cell_list_eq xs ys = (dropWhile (\<lambda>x. x = Bk)(rev xs)  = dropWhile (\<lambda>y. y = Bk) (rev ys))"


lemma tape_to_nat_app_bk[simp]: "tape_to_nat (xs @ [Bk]) = tape_to_nat xs"
  apply(induct xs)
   apply(auto)
  done

lemma is_cell_list_eq_same[simp]: "is_cell_list_eq xs xs"
  apply(induct xs)
   apply(auto)
  done

lemma is_cell_list_eq_com: "is_cell_list_eq xs ys \<Longrightarrow> is_cell_list_eq ys xs"
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
  by (simp add: tape_to_nat_inverse)
lemma decode_encode_inverse: 
  assumes encoded_decoded: "(z1,x1,y1) = decode_tape(encode_tape(z,x,y))"
  shows "z=z1 \<and> is_cell_list_eq x x1 \<and> is_cell_list_eq y y1"
  using encoded_decoded nat_to_tape_inverse by auto




end