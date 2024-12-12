/// -*- coding:utf-8 -*-
/// title       : Quadrants
/// kata UUID   : 643af0fa9fa6c406b47c5399
/// tags        : ['Fundamentals', 'Mathematics', 'Geometry']
/// ---------------------------------------------------
/// description : solutions for codewars.com
/// author      : solweo
/// -----------------------------------------------------
mod quadrants {
    #[allow(dead_code)]
    fn quadrant(x: i32, y: i32) -> i32 {
        match (x > 0, y > 0) {
            (false, false) => 3,
            (false, true) => 2,
            (true, false) => 4,
            (true, true) => 1,
        }
    }

    #[test]
    fn fixed_tests() {
        assert_eq!(quadrant(1, 2), 1);
        assert_eq!(quadrant(3, 5), 1);
        assert_eq!(quadrant(-10, 100), 2);
        assert_eq!(quadrant(-1, -9), 3);
        assert_eq!(quadrant(19, -56), 4);    
    }
}

/// -*- coding:utf-8 -*-
/// title       : Gravity Flip
/// kata UUID   : 5f70c883e10f9e0001c89673
/// tags        : ['Puzzles', 'Arrays']
/// ---------------------------------------------------
/// description : solutions for codewars.com
/// author      : solweo
/// -----------------------------------------------------
mod gravity_flip {
    #[allow(dead_code)]
    fn flip(dir: char, cubes: &[u32]) -> Vec<u32> {
        let mut cubes = Vec::from(cubes);
        match dir {
            'R' => cubes.sort(),
            'L' => cubes.sort_by(|a, b| b.cmp(a)),
            _ => panic!("Unknown direction: {}", dir),
        }
        cubes
    }

    #[test]
    fn sample_tests() {
        assert_eq!(flip('R', &[3, 2, 1, 2]), vec![1, 2, 2, 3]);
        assert_eq!(flip('L', &[1, 4, 5, 3, 5]), vec![5, 5, 4, 3, 1]);
    }
}

/// -*- coding:utf-8 -*-
/// title       : Quadratic Coefficients Solver
/// kata UUID   : 5d59576768ba810001f1f8d6
/// tags        : ['Fundamentals', 'Mathematics', 'Algebra']
/// ---------------------------------------------------
/// description : solutions for codewars.com
/// author      : solweo
/// -----------------------------------------------------
mod quadratic_coefficients_solver {
    #[allow(dead_code)]
    pub fn quadratic(x1: i32, x2: i32) -> (i32, i32, i32) {
        (1, -x1 - x2, x1 * x2)
    }

    #[test]
    fn example_tests() {
        assert_eq!(quadratic(0, 1), (1, -1, 0));
        assert_eq!(quadratic(1, 1), (1, -2, 1));
        assert_eq!(quadratic(-4, -9), (1, 13, 36));
        assert_eq!(quadratic(-5, -4), (1, 9, 20));
        assert_eq!(quadratic(4, -9), (1, 5, -36));
        assert_eq!(quadratic(5, -4), (1, -1, -20));
    }
}

/// -*- coding:utf-8 -*-
/// title       : Quarter of the year
/// kata UUID   : 5ce9c1000bab0b001134f5af
/// tags        : ['Fundamentals', 'Mathematics']
/// ---------------------------------------------------
/// description : solutions for codewars.com
/// author      : solweo
/// -----------------------------------------------------
mod quarter_of_the_year {
    #[allow(dead_code)]
    fn quarter_of(month: u8) -> u8 {
        (month as f32 / 3.0).ceil() as u8
    }

    #[test]
    fn basic() {
        assert_eq!(quarter_of(3), 1, "Month 3 = quarter 1");
        assert_eq!(quarter_of(8), 3, "Month 8 = quarter 3");
        assert_eq!(quarter_of(11), 4, "Month 11 = quarter 4");
    }  
}

/// -*- coding:utf-8 -*-
/// title       : A wolf in sheep's clothing
/// kata UUID   : 5c8bfa44b9d1192e1ebd3d15
/// tags        : ['Fundamentals', 'Arrays']
/// ---------------------------------------------------
/// description : solutions for codewars.com
/// author      : solweo
/// -----------------------------------------------------
mod a_wolf_in_sheeps_clothing {
    #[allow(dead_code)]
    fn warn_the_sheep(queue: &[&str]) -> String {
        match queue.iter().rev().position(|&a| a == "wolf") {
            None => panic!("There is no wolf in the herd of sheep"),
            Some(position) => match position {
                0 => String::from("Pls go away and stop eating my sheep"),
                other => format!("Oi! Sheep number {}! You are about to be eaten by a wolf!", other),
            },
        }
    }

    #[test]
    fn basic() {
        assert_eq!(
            warn_the_sheep(&["wolf"]),
            "Pls go away and stop eating my sheep",
        );
        assert_eq!(
            warn_the_sheep(&["sheep", "sheep", "sheep", "sheep", "sheep", "wolf", "sheep", "sheep"]),
            "Oi! Sheep number 2! You are about to be eaten by a wolf!",
        );
        assert_eq!(
            warn_the_sheep(&["sheep", "wolf", "sheep", "sheep", "sheep", "sheep", "sheep"]),
            "Oi! Sheep number 5! You are about to be eaten by a wolf!",
        );
        assert_eq!(
            warn_the_sheep(&["wolf", "sheep", "sheep", "sheep", "sheep", "sheep", "sheep"]),
            "Oi! Sheep number 6! You are about to be eaten by a wolf!",
        );
        assert_eq!(
            warn_the_sheep(&["sheep", "wolf", "sheep"]),
            "Oi! Sheep number 1! You are about to be eaten by a wolf!",
        );
        assert_eq!(
            warn_the_sheep(&["sheep", "sheep", "wolf"]),
            "Pls go away and stop eating my sheep",
        );
    }  
}

/// -*- coding:utf-8 -*-
/// title       : Total amount of points
/// kata UUID   : 5bb904724c47249b10000131
/// tags        : ['Fundamentals', 'Arrays', 'Strings']
/// ---------------------------------------------------
/// description : solutions for codewars.com
/// author      : solweo
/// -----------------------------------------------------
mod total_amount_of_points {
    use std::cmp::Ordering;

    #[allow(dead_code)]
    fn points(games: &[String]) -> u32 {
        let mut points: u32 = 0;

        for session in games {
            let left = session[..1].parse::<u8>().unwrap();
            let rigth = session[2..].parse::<u8>().unwrap();

            match left.cmp(&rigth) {
                Ordering::Equal => points += 1,
                Ordering::Greater => points += 3,
                Ordering::Less => {},
            }
        }

        points
    }

    #[test]
    fn fixed_tests() {
        const ERR_MSG: &str = "\nYour result (left) did not match the expected output (right)";
    
        fn do_fixed_test(e: &[&str], expected: u32) {
            let a = &e.iter().map(|x| x.to_string()).collect::<Vec<_>>();
            assert_eq!(points(a), expected, "{ERR_MSG} with games = {a:?}")
        }

        do_fixed_test(&["1:0", "2:0", "3:0", "4:0", "2:1", "3:1", "4:1", "3:2", "4:2", "4:3"], 30);
        do_fixed_test(&["1:1", "2:2", "3:3", "4:4", "2:2", "3:3", "4:4", "3:3", "4:4", "4:4"], 10);
        do_fixed_test(&["0:1", "0:2", "0:3", "0:4", "1:2", "1:3", "1:4", "2:3", "2:4", "3:4"], 0);
        do_fixed_test(&["1:0", "2:0", "3:0", "4:0", "2:1", "1:3", "1:4", "2:3", "2:4", "3:4"], 15);
        do_fixed_test(&["1:0", "2:0", "3:0", "4:4", "2:2", "3:3", "1:4", "2:3", "2:4", "3:4"], 12);
    }  
}

/// -*- coding:utf-8 -*-
/// title       : Sum of differences in array
/// kata UUID   : 5b73fe9fb3d9776fbf00009e
/// tags        : ['Arrays', 'Fundamentals']
/// ---------------------------------------------------
/// description : solutions for codewars.com
/// author      : solweo
/// -----------------------------------------------------
mod sum_of_differences_in_array {
    use itertools::Itertools;

    #[allow(dead_code)]
    fn sum_of_differences(arr: &[i8]) -> Option<i8> {
        if arr.len() < 2 { None }

        else { Some( arr.iter()
            .sorted_by(|a, b| b.cmp(a))
            .tuple_windows()
            .map(|(a, b)| a - b)
            .sum(),
        ) }
    }

    #[test]
    fn sample_tests() {
        const ERR_MSG: &str = "\nYour result (left) did not match the expected output (right)";

        assert_eq!(sum_of_differences(&[1, 2, 10]), Some(9), "{}", ERR_MSG);
        assert_eq!(sum_of_differences(&[-3, -2, -1]), Some(2), "{}", ERR_MSG);
        assert_eq!(sum_of_differences(&[1, 1, 1, 1, 1]), Some(0), "{}", ERR_MSG);
        assert_eq!(sum_of_differences(&[-17, 17]), Some(34), "{}", ERR_MSG);
        assert_eq!(sum_of_differences(&[]), None, "{}", ERR_MSG);
        assert_eq!(sum_of_differences(&[0]), None, "{}", ERR_MSG);
        assert_eq!(sum_of_differences(&[-1]), None, "{}", ERR_MSG);
        assert_eq!(sum_of_differences(&[1]), None, "{}", ERR_MSG);
    }
}

/// -*- coding:utf-8 -*-
/// title       : If you can't sleep, just count sheep!!
/// kata UUID   : 5b077ebdaf15be5c7f000077
/// tags        : ['Fundamentals', 'Strings']
/// ---------------------------------------------------
/// description : solutions for codewars.com
/// author      : solweo
/// -----------------------------------------------------
mod if_you_cant_sleep_just_count_sheep {
    #[allow(dead_code)]
    fn count_sheep(n: u32) -> String {
        (1 ..= n).fold(String::new(), |acc, i| format!("{acc}{i} sheep..."))
    }

    #[test]
    fn returns_expected() {
        assert_eq!(count_sheep(0), "");
        assert_eq!(count_sheep(1), "1 sheep...");
        assert_eq!(count_sheep(2), "1 sheep...2 sheep...");
        assert_eq!(count_sheep(3), "1 sheep...2 sheep...3 sheep...");
    }
}

/// -*- coding:utf-8 -*-
/// title       : Expressions Matter
/// kata UUID   : 5ae62fcf252e66d44d00008e
/// tags        : ['Fundamentals', 'Algorithms']
/// ---------------------------------------------------
/// description : solutions for codewars.com
/// author      : solweo
/// -----------------------------------------------------
mod expressions_matter {
    #[allow(dead_code)]
    fn expressions_matter(a: u64, b: u64, c: u64) -> u64 {
        let cmd = |q: Vec<(u64, u64)>| -> Vec<u64> {
            q.iter().map(|(x, y)|
                std::cmp::max(x + y, x * y)
            ).collect()
        };

        let v = cmd(vec![(a, b), (b, c)]);
        let v = cmd(vec![(a, v[1]), (v[0], c)]);
        
        v[0].max(v[1])
    }

    #[test]
    fn basic_tests() {
        assert_eq!(expressions_matter(2, 1, 2), 6);
        assert_eq!(expressions_matter(1, 1, 1), 3);
        assert_eq!(expressions_matter(2, 1, 1), 4);
        assert_eq!(expressions_matter(1, 2, 3), 9);
        assert_eq!(expressions_matter(1, 3, 1), 5);
        assert_eq!(expressions_matter(2, 2, 2), 8);

        assert_eq!(expressions_matter(5, 1, 3), 20);
        assert_eq!(expressions_matter(3, 5, 7), 105);
        assert_eq!(expressions_matter(5, 6, 1), 35);
        assert_eq!(expressions_matter(1, 6, 1), 8);
        assert_eq!(expressions_matter(2, 6, 1), 14);
        assert_eq!(expressions_matter(6, 7, 1), 48);

        assert_eq!(expressions_matter(2, 10, 3), 60);
        assert_eq!(expressions_matter(1, 8, 3), 27);
        assert_eq!(expressions_matter(9, 7, 2), 126);
        assert_eq!(expressions_matter(1, 1, 10), 20);
        assert_eq!(expressions_matter(9, 1, 1), 18);
        assert_eq!(expressions_matter(10, 5, 6), 300);
        assert_eq!(expressions_matter(1, 10, 1), 12);        
    }
}

/// -*- coding:utf-8 -*-
/// title       : The Feast of Many Beasts
/// kata UUID   : 5aa736a455f906981800360d
/// tags        : ['Strings', 'Fundamentals']
/// ---------------------------------------------------
/// description : solutions for codewars.com
/// author      : solweo
/// -----------------------------------------------------
mod the_feast_of_many_beasts {
    #[allow(dead_code)]
    fn feast(beast: &str, dish: &str) -> bool {
        let c = (beast.as_bytes(), dish.as_bytes());
        c.0.first() == c.1.first() && c.0.last() == c.1.last()
    }

    #[test]
    fn sample_test_cases() {
        assert!(feast("great blue heron", "garlic naan"));
        assert!(feast("chickadee", "chocolate cake"));
        assert!(!feast("brown bear", "bear claw"));
    }
}

/// -*- coding:utf-8 -*-
/// title       : Dollars and Cents
/// kata UUID   : 5aa736a455f906981800360d
/// tags        : ['Functional Programming', 'Strings', 'Algorithms']
/// ---------------------------------------------------
/// description : solutions for codewars.com
/// author      : solweo
/// -----------------------------------------------------
mod dollars_and_cents {
    #[allow(dead_code)]
    fn format_money(amount: f64) -> String {
        format!("${:.2}", amount)
    }

    #[test]
    fn basic() {
        assert_eq!(format_money(39.99), "$39.99");
        assert_eq!(format_money(3.0), "$3.00");
        assert_eq!(format_money(3.10), "$3.10");
        assert_eq!(format_money(314.16), "$314.16");
    }
}

/// -*- coding:utf-8 -*-
/// title       : The 'if' function
/// kata UUID   : 54147087d5c2ebe4f1000805
/// tags        : ['Functional Programming', 'Fundamentals']
/// ---------------------------------------------------
/// description : solutions for codewars.com
/// author      : solweo
/// -----------------------------------------------------
mod the_if_function {
    #[allow(dead_code)]
    fn _if<T, F1, F2>(cond: bool, mut then: F1, mut els: F2) -> T
    where F1: FnMut() -> T, F2: FnMut() -> T
    {
    match cond {
            true => then(),
            false => els(),
        }
    }

    #[test]
    fn should_support_true() {
        assert_eq!(_if(true, || 1, || 2), 1);
    }

    #[test]
    fn should_support_false() {
        assert_eq!(_if(false, || 1, || 2), 2);
    }

    #[test]
    fn should_support_false_other_type() {
        assert_eq!(_if(false, || 'a', || 'b'), 'b');
        assert_eq!(_if(true, || "True", || "False"), "True");
    }
}

/// -*- coding:utf-8 -*-
/// title       : Collinearity
/// kata UUID   : 65ba420888906c1f86e1e680
/// tags        : ['Fundamentals', 'Geometry', 'Mathematics', 'Data Science', 'Games']
/// ---------------------------------------------------
/// description : solutions for codewars.com
/// author      : solweo
/// -----------------------------------------------------
#[allow(dead_code)]
mod collinearity {
    fn collinearity(x1: i32, y1: i32, x2: i32, y2: i32) -> bool {
        let cross_product = x1 * y2 - x2 * y1;
        cross_product == 0
    }

    fn do_test(x1: i32, y1: i32, x2: i32, y2: i32, expected: bool) {
        assert_eq!(
            collinearity(x1, y1, x2, y2),
            expected,
            "Input: ({x1}, {y1}, {x2}, {y2})"
        );
    }

    #[test]
    fn test_fixed_one_direction() {
        do_test(1, 1, 1, 1, true);
        do_test(1, 2, 2, 4, true);
        do_test(1, 2, 3, 7, false);
    }

    #[test]
    fn test_fixed_opposite_direction() {
        do_test(1, 1, 6, 1, false);
        do_test(1, 2, -1, -2, true);
        do_test(1, 2, 1, -2, false);
    }

    #[test]
    fn test_fixed_vectors_contain_zero() {
        do_test(4, 0, 11, 0, true);
        do_test(0, 1, 6, 0, false);
        do_test(4, 4, 0, 4, false);
    }

    #[test]
    fn test_fixed_vector_with_0_0_coordinates() {
        do_test(0, 0, 0, 0, true);
        do_test(0, 0, 1, 0, true);
        do_test(5, 7, 0, 0, true);
    }
}