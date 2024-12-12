/// -*- coding:utf-8 -*-
/// title       : Vowel Count
/// kata UUID   : 54ff3102c1bad923760001f3
/// tags        : ['Strings', 'Fundamentals']
/// ---------------------------------------------------
/// description : solutions for codewars.com
/// author      : solweo
/// -----------------------------------------------------
mod vowel_count {
    #[allow(dead_code)]
    fn get_count(s: &str) -> usize {
        s.matches(['a', 'e', 'i', 'o', 'u']).count()
    }

    #[test]
    fn my_tests() {
        assert_eq!(get_count("abracadabra"), 5);
    }
}

/// -*- coding:utf-8 -*-
/// title       : Disemvowel Trolls
/// kata UUID   : 52fba66badcd10859f00097e
/// tags        : ['Strings', 'Regular Expressions', 'Fundamentals']
/// ---------------------------------------------------
/// description : solutions for codewars.com
/// author      : solweo
/// -----------------------------------------------------
mod disemvowel_trolls {
    #[allow(dead_code)]
    fn disemvowel(s: &str) -> String {
        s.chars().filter(|&c| !"aeiuoAEIUO".contains(c)).collect::<String>()
    }

    #[test]
    fn example_test() {
        assert_eq!(disemvowel("This website is for losers LOL!"), "Ths wbst s fr lsrs LL!");
    }
}

/// -*- coding:utf-8 -*-
/// title       : Bubblesort Once
/// kata UUID   : 56b97b776ffcea598a0006f2
/// tags        : ['Algorithms', 'Tutorials', 'Sorting']
/// ---------------------------------------------------
/// description : solutions for codewars.com
/// author      : solweo
/// -----------------------------------------------------
mod bubblesort_once {
    #[allow(dead_code)]
    fn bubblesort_once(lst: &[u32]) -> Vec<u32> {
        let mut ans = Vec::new();
        lst.iter().for_each(|el| {
            if ans.is_empty() || el > ans.last().unwrap() { ans.push(*el); }
            else { ans.insert(ans.len() - 1, *el) }
        });
        ans
    }

    #[test]
    fn example_test() {
        fn dotest(a: &[u32], expected: &[u32]) {
            let actual = bubblesort_once(a);
            assert!(actual == expected, 
                "With a = {a:?}\nExpected {expected:?} but got {actual:?}")
        }

        dotest(&[9, 7, 5, 3, 1, 2, 4, 6, 8], &[7, 5, 3, 1, 2, 4, 6, 8, 9]);
    }
}

/// -*- coding:utf-8 -*-
/// title       : Find the next perfect square!
/// kata UUID   : 56269eb78ad2e4ced1000013
/// tags        : ['Algebra', 'Fundamentals']
/// ---------------------------------------------------
/// description : solutions for codewars.com
/// author      : solweo
/// -----------------------------------------------------
mod find_the_next_perfect_square {
    #[allow(dead_code)]
    fn find_next_square(sq: u64) -> Option<u64> {
        let root = (sq as f64).sqrt();
        if root.fract() != 0. { return None } 
        Some((root as u64 + 1).pow(2))
    }
    
    #[test]
    fn sample_tests() {
        fn do_test(n: u64, expected: Option<u64>) {
            let actual = find_next_square(n);
            assert_eq!(actual, expected, "\nYour result (left), did not match the correct answer (right) for n = {n}");
        }

        do_test(121, Some(144));
        do_test(625, Some(676));
        do_test(319_225, Some(320_356));
        do_test(15_241_383_936, Some(15_241_630_849));
        do_test(155, None);
        do_test(342_786_627, None);
    }
}

/// -*- coding:utf-8 -*-
/// title       : Nth power rules them all!
/// kata UUID   : 58aed2cafab8faca1d000e20
/// tags        : ['Algebra', 'Fundamentals']
/// ---------------------------------------------------
/// description : solutions for codewars.com
/// author      : solweo
/// -----------------------------------------------------
mod nth_power_rules_them_all {
    #[allow(dead_code)]
    fn modified_sum(array: &[i32], power: u32) -> i32 {
        array.iter().fold(0i32,|acc, &el| acc + el.pow(power) - el)
    }
    
    #[test]
    fn test_add() {
        assert_eq!(modified_sum(&[1, 2, 3], 3), 30);
        assert_eq!(modified_sum(&[1, 2], 5), 30);
    }
}

/// -*- coding:utf-8 -*-
/// title       : Multiples By Permutations II
/// kata UUID   : 58aed2cafab8faca1d000e20
/// tags        : ['Fundamentals', 'Data Structures', 'Strings', 'Mathematics', 'Algebra', 'Sorting', 'Combinatorics']
/// ---------------------------------------------------
/// description : solutions for codewars.com
/// author      : solweo
/// -----------------------------------------------------
mod multiples_by_permutations_ii {
    use itertools::Itertools;

    #[allow(dead_code)]
    fn find_lowest_int(k: u64) -> u64 {
        let unify = |num: u64| { num.to_string().chars().sorted().join("") };
        (9..).step_by(9).find(|n| unify(n*k) == unify(n*(k+1)) ).unwrap_or(0)
    }

    #[test]
    fn fixed_tests() {
        fn dotest(n: u64, expected: u64) {
            let actual = find_lowest_int(n);
            assert!(actual == expected, 
                "With k = {n}\nExpected {expected} but got {actual}")
        }

        dotest(325,477);
        dotest(599,2394);
        dotest(855, 999);
        dotest(1,125874);
        dotest(100,8919);
        dotest(1000,89919);
        dotest(10000,899919);
    }
}

/// -*- coding:utf-8 -*-
/// title       : Build a square
/// kata UUID   : 59a96d71dbe3b06c0200009c
/// tags        : ['Fundamentals', 'ASCII Art']
/// ---------------------------------------------------
/// description : solutions for codewars.com
/// author      : solweo
/// -----------------------------------------------------
#[allow(dead_code)]
mod build_a_square {
    fn generate_shape(n: i32) -> String {
        ("+".repeat(n as usize) + "\n")
            .repeat(n as usize)
            .trim()
            .to_string()
    }

    fn dotest(n: i32, expected: &str) {
        let actual = generate_shape(n);
        assert!(actual == expected, 
            "With n = {n}\nExpected \"{expected}\" but got \"{actual}\"")
    }
    
    #[test]
    fn sample_test() {
      dotest(3, "+++\n+++\n+++")
    }
}