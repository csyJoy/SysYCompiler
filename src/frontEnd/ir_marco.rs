use parser::add_branch_count;
use parser::add_reg_idx;
use crate::frontEnd::parser;

pub fn land_code_gen(s1_reg: i32, s2_reg: i32, s1_string: String, s2_string: String) -> String {
        let branch_count = add_branch_count();
        let result = format!("\talloc @result_{} i32\n", branch_count);
        let store_result = format!("\tstore 0 @result_{}\n", branch_count);
        let branch = format!("\tbr %{}, %then_{}, %else_{}\n", s1_reg, branch_count, branch_count);
        let then_case = format!("%then_{}:\n", branch_count);
        let then_string = s2_string + &format!("\tstore %{}, @result_{}\n", s2_reg, branch_count)
            + &format!("\tjump %end_{}\n", branch_count);
        let else_case = format!("%else_{}:\n", branch_count);
        let else_string = format!("\tjump %end_{}\n", branch_count);
        let end_case = format!("%end_{}:\n", branch_count);
        let end_string = format!("\t%{} = load @result_{}\n", add_reg_idx(), branch_count);
        result + &store_result + &s1_string + &branch + &then_case + &then_string + &else_case +
        &else_string + &end_case + &end_string
}
pub fn lor_code_gen(s1_reg: i32, s2_reg: i32, s1_string: String, s2_string: String) -> String {
        let branch_count = add_branch_count();
        let result = format!("\talloc @result_{} i32\n", branch_count);
        let store_result = format!("\tstore 1 @result_{}\n", branch_count);
        let branch = format!("\tbr %{}, %then_{}, %else_{}\n", s1_reg, branch_count, branch_count);
        let then_case = format!("%then_{}:\n", branch_count);
        let then_string = format!("\tjump %end_{}\n", branch_count);
        let else_case = format!("%else_{}:\n", branch_count);
        let else_string = s2_string + &format!("\tstore %{}, @result_{}\n", s2_reg, branch_count)
            + &format!("\tjump %end_{}\n", branch_count);
        let end_case = format!("%end_{}:\n", branch_count);
        let end_string = format!("\t%{} = load @result_{}\n", add_reg_idx(), branch_count);
        result + &store_result + &s1_string + &branch + &then_case + &then_string + &else_case +
            &else_string + &end_case + &end_string
}