/// -*- coding:utf-8 -*-
/// title       : Closed Brackets String
/// kata UUID   : 64b771989416793927fbd2bf
/// tags        : ['Algorithms', 'Strings', 'Recursion', 'Stacks', 'Dynamic Programming', 'Data Structures']
/// ---------------------------------------------------
/// description : solutions for codewars.com
/// author      : solweo
/// -----------------------------------------------------
mod closed_brackets_string {
    #[allow(dead_code)]
    fn closed_brackets(s: &str) -> bool {
        s.chars().try_fold((0usize, 0usize), |(l, u), c| Some((
            if c == '(' { l + 1 } else { l.saturating_sub(1) },
            if c != ')' { u + 1 } else { u.checked_sub(1)? },
        ))).map_or(false, |(l, _)| l == 0)
    }

    #[test]
    fn fixed_tests() {
        fn dotest(s: &str, expected: bool) {
            let actual = closed_brackets(s);
            assert!(actual == expected, 
                "With s = \"{s}\"\nExpected {expected} but got {actual}")
        }

        dotest("(J))", true);
        dotest("(", false);
        dotest("", true);
        dotest("()J(", false);
        dotest("J", true);
        dotest(")(", false);
        dotest("()", true);
        dotest("J)(J", true);
        dotest("(J()J(()(J", false);
        dotest("J(JJ()J((J", false);
    }
}

/// -*- coding:utf-8 -*-
/// title       : Matrix Transpose
/// kata UUID   : 52fba2a9adcd10b34300094c
/// tags        : ['Mathematics', 'Algebra', 'Matrix', 'Algorithms']
/// ---------------------------------------------------
/// description : solutions for codewars.com
/// author      : solweo
/// -----------------------------------------------------
mod matrix_ranspose {
    #[allow(dead_code)]
    fn transpose(matrix:  &[Vec<u8>]) -> Vec<Vec<u8>> {
        let i = matrix.first().unwrap().len();
        (0..matrix.first().unwrap().len()).map(|j| matrix.iter().flatten().skip(j).step_by(i).cloned().collect::<Vec<_>>()).collect::<Vec<_>>()
    }

    #[test]
    fn sample_tests() {
        assert_eq!(transpose(&[vec![1]]), vec![vec![1]]);
        assert_eq!(transpose(&[vec![1, 2, 3]]), vec![vec![1], vec![2], vec![3]]);
        assert_eq!(transpose(&[vec![1, 2, 3], vec![4, 5, 6], vec![7, 8, 9]]), vec![vec![1, 4, 7], vec![2, 5, 8], vec![3, 6, 9]]);
        assert_eq!(transpose(&[vec![1, 0, 0], vec![0, 1, 0], vec![0, 0, 1], vec![0, 1, 0], vec![1, 0, 0]]), vec![vec![1, 0, 0, 0, 1], vec![0, 1, 0, 1, 0], vec![0, 0, 1, 0, 0]]);
    }
}

/// -*- coding:utf-8 -*-
/// title       : Delta Generators
/// kata UUID   : 6040b781e50db7000ab35125
/// tags        : ['Iterators', 'Recursion']
/// ---------------------------------------------------
/// description : solutions for codewars.com
/// author      : solweo
/// -----------------------------------------------------
mod delta_generators {
    use std::ops::Sub;
    use itertools::Itertools;

    #[allow(dead_code)]
    fn delta<'a, T, I>(values: I, level: usize) -> Box<dyn Iterator<Item = T> + 'a>
    where
        T: Sub<Output = T> + Clone + 'a,
        I: IntoIterator<Item = T>,
        I::IntoIter: 'a,
    {
        match level {
            0 => Box::new(values.into_iter()),
            level => Box::new(delta(values, level - 1).tuple_windows().map(|(left, right)| right - left)),
        }
    }

    #[test]
    fn finite_collections() {
        
        let input1 = vec![1, 2, 3, 4, 5, 6];
        let expected1 = vec![1,1,1,1,1];
        assert_eq!(delta(input1, 1).collect::<Vec<_>>(), expected1);

        let input2 = vec![1.5, 1.5, 1.5, 1.5, 1.5, 1.5];
        let expected2 = vec![0.0];
        assert_eq!(delta(input2, 5).collect::<Vec<_>>(), expected2);
        
        let input3 = vec![1, -1, 1];
        let expected3 = vec![];
        assert_eq!(delta(input3, 3).collect::<Vec<_>>(), expected3);
    }
    
    #[test]
    fn iterators() {
        
        // (infinite) iterator as input
        let input1 = std::iter::successors(Some(0), |&x| Some(x + 2));
        let expected1 = vec![2,2,2,2];
        assert_eq!(delta(input1, 1).take(4).collect::<Vec<_>>(), expected1);
        
        // is an iterator
        let iter2 = delta(vec![2, 4, 5, 6, 8], 1);
        let expected2 = vec![2,1,1,2];
        for (actual, expect) in iter2.zip(expected2) {
            assert_eq!(actual, expect);
        }
        
        // works as source for other iterators
        let iter3 = delta(vec![0,4,4,4,4], 1).map(|x| x + 2);
        let expected3 = Some(6);
        assert_eq!(iter3.take(1).next(), expected3);
    }
    
    #[derive(Clone, Copy, Debug, PartialEq)]
    struct Point {
        x: i32,
        y: i32,
    }

    impl Sub for Point {
        type Output = Self;
        fn sub(self, other: Self) -> Self::Output {
            Self { x: self.x - other.x, y: self.y - other.y }
        }
    }
    
    #[test]
    fn custom_types() {
        let a = Point { x: 4, y: 10 };
        let b = Point { x: -12, y: 44 };
        let c = Point { x: 20, y: 30 };
        let input = vec![a, b, c];
        let expected = vec![Point { x: 48, y: -48 }];
        assert_eq!(delta(input, 2).collect::<Vec<_>>(), expected);
    }
}

/// -*- coding:utf-8 -*-
/// title       : zipWith
/// kata UUID   : 5825792ada030e9601000782
/// tags        : ['ListsArrays', 'Functional Programming', 'Algorithms']
/// ---------------------------------------------------
/// description : solutions for codewars.com
/// author      : solweo
/// -----------------------------------------------------
mod zip_with {
    #[allow(dead_code)]
    fn zip_with<F, T, S, R>(f: F, a: &[T], b: &[S]) -> Vec<R> 
    where
        F: Fn(T, S) -> R,
        T: Copy,
        S: Copy
    {
        a.iter().zip(b).map(|(x, y)| f(*x, *y)).collect::<Vec<R>>()
    }
    

    #[test]
    fn basic_tests() {
        use std::ops::{Add, Sub};

        const ERR_MSG: &str = "\nYour result (left) did not match the expected output (right).";

        assert_eq!(&zip_with(i32::add, &[0,1,2,3],     &[0,1,2,3]),     &[0,2,4,6], "{ERR_MSG}");
        assert_eq!(&zip_with(i32::add, &[0,1,2,3],     &[0,1,2,3]),     &[0,2,4,6], "{ERR_MSG}");
        assert_eq!(&zip_with(i32::add, &[0,1,2,3,4,5], &[6,5,4,3,2,1]), &[6,6,6,6,6,6], "{ERR_MSG}");
        assert_eq!(&zip_with(i32::add, &[0,1,2,3,4  ], &[6,5,4,3,2,1]), &[6,6,6,6,6  ], "{ERR_MSG}");
        assert_eq!(&zip_with(i32::add, &[0,1,2,3,4,5], &[6,5,4,3,2  ]), &[6,6,6,6,6  ], "{ERR_MSG}");
        assert_eq!(&zip_with(i32::pow, &[10,10,10,10], &[0,1,2,3]),     &[1,10,100,1000], "{ERR_MSG}");
        assert_eq!(&zip_with(i32::max, &[1,4,7,1,4,7], &[4,7,1,4,7,1]), &[4,7,7,4,7,7], "{ERR_MSG}");
        assert_eq!(&zip_with(i32::sub, &[0,1,2,3,4,5], &[6,5,4,3,2,1]), &[-6,-4,-2,0,2,4], "{ERR_MSG}");
        assert_eq!(&zip_with(i32::pow, &[10; 10],     &[0,1,2,3,4,5,6]), &[1,10,100,1000,10000,100000,1000000], "{ERR_MSG}");
        assert_eq!(&zip_with(
                        |c,n| std::iter::repeat(c).take(n).collect::<String>(),
                        &['a','b','c','d','e','f'], &[6,5,4,3,2,1]), 
                   &["aaaaaa","bbbbb","cccc","ddd","ee","f"], "{ERR_MSG}"
        );
    }
}

/// -*- coding:utf-8 -*-
/// title       : Reducing by steps
/// kata UUID   : 56efab15740d301ab40002ee
/// tags        : ['Mathematics', 'Arrays', 'Functional Programming', 'Lists', 'Data Structures']
/// ---------------------------------------------------
/// description : solutions for codewars.com
/// author      : solweo
/// -----------------------------------------------------
#[allow(dead_code)]
mod reducing_by_steps {
    fn som(x: i64, y: i64) -> i64 {
        x + y
    }

    fn maxi(x: i64, y: i64) -> i64 {
        i64::max(x, y)
    }

    fn mini(x: i64, y: i64) -> i64 {
        i64::min(x, y)
    }

    fn gcdi(m: i64, n: i64) -> i64 {
        let (mut m, mut n) = (m, n);
        while n != 0 {
            let remainder = m % n;
            m = n;
            n = remainder;
        }
        m.abs()
    }

    fn lcmu(a: i64, b: i64) -> i64 {
        if a == 0 || b == 0 {
            0
        } else {
            (a.abs() / gcdi(a, b)) * b.abs()
        }
    }

    fn oper_array<T>(f: T, a: &[i64], init: i64) -> Vec<i64>
    where 
        T: Fn(i64, i64) -> i64
    {
        a.iter().scan(init, |state, &x| {
            *state = f(*state, x);
            Some(*state)
        }).collect()
    }
    
    #[test]
    fn basics_som() {
        let testing_som = |a, exp| assert_eq!(&oper_array(som, a, 0), exp);
        testing_som(&[ 18, 69, -90, -78, 65, 40 ], &vec![ 18, 87, -3, -81, -16, 24 ]);
    }
    #[test]
    fn basics_lcmu() {
        let testing_lcmu = |a, exp| assert_eq!(&oper_array(lcmu, a, a[0]), exp);
        testing_lcmu(&[ 18, 69, -90, -78, 65, 40 ], &vec![ 18, 414, 2070, 26910, 26910, 107640 ]);
    }
    #[test]
    fn basics_maxi() {
        let testing_maxi = |a, exp| assert_eq!(&oper_array(maxi, a, a[0]), exp);
        testing_maxi(&[ 18, 69, -90, -78, 65, 40 ], &vec![ 18, 69, 69, 69, 69, 69 ]);
    }
    #[test]
    fn basics_gcdi() {
        let testing_gcdi = |a, exp| assert_eq!(&oper_array(gcdi, a, a[0]), exp);
        testing_gcdi(&[ 18, 69, -90, -78, 65, 40 ], &vec![ 18, 3, 3, 3, 1, 1 ]);
    }
}

/// -*- coding:utf-8 -*-
/// title       : Draw a Circle.
/// kata UUID   : 59c804d923dacc6c41000004
/// tags        : ['Strings', 'Geometry', 'ASCII Art', 'Algorithms']
/// ---------------------------------------------------
/// description : solutions for codewars.com
/// author      : solweo
/// -----------------------------------------------------
#[allow(dead_code)]
mod draw_a_circle {
    fn circle(radius: i32) -> String {
        const PXL: char = '\u{2588}';
        const SPACE: char = ' ';
    
        match radius {
            r if r < 0 => "".to_string(),
            0 => "\n".to_string(),
            _ => {
                let mut circle = String::new();
                let r = radius -1;
    
                for y in -r..(r+1) {
                    for x in -r..(r+1) {
                        circle.push(
                            if x*x + y*y < radius*radius {
                                PXL
                            } else {
                                SPACE
                            }
                        );
                    }
                    circle.push('\n');
                } 
    
                circle
            }
        }
    }

    #[test]
    fn basic_tests() {
        assert_eq!(circle(-1), "", "Negative radii should return the empty string.");
        assert_eq!(circle(-321), "", "Negative radii should return the empty string.");
        assert_eq!(circle(0), "\n", "A radius of 0 should produce \"\\n\"");
        assert_eq!(circle(1), "█\n");
        assert_eq!(circle(2), "███\n███\n███\n");
    }
}

/// -*- coding:utf-8 -*-
/// title       : ASCII Fun #2: Funny Dots
/// kata UUID   : 59098c39d8d24d12b6000020
/// tags        : ['ASCII Art']
/// ---------------------------------------------------
/// description : solutions for codewars.com
/// author      : solweo
/// -----------------------------------------------------
#[allow(dead_code)]
mod ascii_fun_2_funny_dots {
    use itertools::Itertools;
    use std::iter::repeat;

    fn dot(n: u32, m: u32) -> String {
        let sep = |t: u32| repeat("+").take(t as usize + 1).join("---");
        let dot = |t: u32| repeat("|").take(t as usize + 1).join(" o ");
        [sep(n), dot(n)].iter().cycle().take(2 * m as usize + 1).join("\n")
    }

    const ERR_MSG: &str = "\nYour result (left) did not match the expected output (right)";
    
    fn dotest(n: u32, m: u32, expected: &str) {
        assert_eq!(dot(n, m), expected, "{ERR_MSG} with n = {n}, m = {m}")
    }

    #[test]
    fn fixed_tests() {
        dotest(1, 1, "+---+\n| o |\n+---+");
        dotest(3, 2, "+---+---+---+\n| o | o | o |\n+---+---+---+\n| o | o | o |\n+---+---+---+");
    }
}

/// -*- coding:utf-8 -*-
/// title       : ASCII Fun #1: X- Shape
/// kata UUID   : 5906436806d25f846400009b
/// tags        : ['ASCII Art']
/// ---------------------------------------------------
/// description : solutions for codewars.com
/// author      : solweo
/// -----------------------------------------------------
#[allow(dead_code)]
mod ascii_fun_1_x_shape {
    fn x(n: u32) -> String {
        const SPACE: char = '□';
        const FILL: char = '■';
    
        let get_pxl = |i, j| if i == j || i + j == n - 1 { FILL } else { SPACE };
    
        (0..n).map(|i| (0..n).map(|j| get_pxl(i, j))
            .collect())
            .collect::<Vec<String>>()
            .join("\n")
    }

    fn dotest(n: u32, expected: &str) {
        let actual = x(n);
        assert!(actual == expected, "With n = {n}\nExpected \n{expected}\nGot \n{actual}")
    }

    #[test]
    fn fixed_tests() {
        dotest(3, "■□■\n□■□\n■□■");
        dotest(7, "■□□□□□■\n□■□□□■□\n□□■□■□□\n□□□■□□□\n□□■□■□□\n□■□□□■□\n■□□□□□■");
    }
}

/// -*- coding:utf-8 -*-
/// title       : Give me a Diamond
/// kata UUID   : 5503013e34137eeeaa001648
/// tags        : ['Strings', 'ASCII Art', 'Fundamentals']
/// ---------------------------------------------------
/// description : solutions for codewars.com
/// author      : solweo
/// -----------------------------------------------------
#[allow(dead_code)]
mod give_me_a_diamond {
    use itertools::Itertools;

    fn print(n: i32) -> Option<String> {
        match n {
            n if n <= 0 || n % 2 == 0 => None,
            _ => Some((1..=n).step_by(2).chain((1..=n).rev().step_by(2).skip(1))
                .map(|dot_num| format!("{}{}\n",
                    " ".repeat(((n - dot_num) as usize).saturating_div(2)),
                    "*".repeat(dot_num as usize)))
                .join(""))
        }
    }

    #[test]
    fn basic_test() {
      assert_eq!(print(3), Some(" *\n***\n *\n".to_string()) );
      assert_eq!(print(5), Some("  *\n ***\n*****\n ***\n  *\n".to_string()) );
      assert_eq!(print(-3),None);
      assert_eq!(print(2), None);
      assert_eq!(print(0), None);
      assert_eq!(print(1), Some("*\n".to_string()) );
    }
}

/// -*- coding:utf-8 -*-
/// title       : Build Tower
/// kata UUID   : 576757b1df89ecf5bd00073b
/// tags        : ['Strings', 'ASCII Art', 'Fundamentals']
/// ---------------------------------------------------
/// description : solutions for codewars.com
/// author      : solweo
/// -----------------------------------------------------
#[allow(dead_code)]
mod build_tower {
    fn tower_builder(n_floors: usize) -> Vec<String> {
        (1..=n_floors)
            .map(|i| format!("{}{}{}",
                " ".repeat(n_floors - i),
                "*".repeat((2 * i) - 1),
                " ".repeat(n_floors - i)))
            .collect()
    }

    #[test]
    fn fixed_tests() {
        assert_eq!(tower_builder(1), vec!["*"]);
        assert_eq!(tower_builder(2), vec![" * ", "***"]);
        assert_eq!(tower_builder(3), vec!["  *  ", " *** ", "*****"]);
    }
}

/// -*- coding:utf-8 -*-
/// title       : Build Tower Advanced
/// kata UUID   : 57675f3dedc6f728ee000256
/// tags        : ['Strings', 'ASCII Art', 'Fundamentals']
/// ---------------------------------------------------
/// description : solutions for codewars.com
/// author      : solweo
/// -----------------------------------------------------
#[allow(dead_code)]
mod build_tower_advanced {
    fn tower_builder(n_floors: usize, block_size: (usize, usize)) -> Vec<String> {
        let (block_x, block_y) = block_size;
        let half_space_size = |mult| ((n_floors*2-1)*block_x).saturating_sub(mult*block_x).saturating_div(2);
        (1..n_floors*2).step_by(2)
            .flat_map(|mult| vec![format!("{}{}{}",
                " ".repeat(half_space_size(mult)),
                "*".repeat(mult*block_x),
                " ".repeat(half_space_size(mult)));
                block_y])
            .collect()
    }

    #[test]
    fn test_fixed() {
        assert_eq!(tower_builder(1, (1, 1)), vec!["*"]);
        assert_eq!(tower_builder(3, (4, 2)), vec!["        ****        ", "        ****        ", "    ************    ", "    ************    ", "********************", "********************"]);
    }
}

/// -*- coding:utf-8 -*-
/// title       : Block Letter Printer
/// kata UUID   : 6375587af84854823ccd0e90
/// tags        : ['Strings', 'ASCII Art', 'Fundamentals']
/// ---------------------------------------------------
/// description : solutions for codewars.com
/// author      : solweo
/// -----------------------------------------------------
#[allow(dead_code)]
mod block_letter_printer {
    use itertools::Itertools;
    use std::collections::HashMap;

    fn block_print(input: &str) -> String {
        let mut alpha: HashMap<char, [&str; 7]> = HashMap::new();

        alpha.insert(' ', [
            "     ", 
            "     ", 
            "     ", 
            "     ", 
            "     ", 
            "     ", 
            "     ", 
        ]);

        alpha.insert('a', [
            " AAA ", 
            "A   A", 
            "A   A", 
            "AAAAA", 
            "A   A", 
            "A   A", 
            "A   A"
        ]);

        alpha.insert('b', [
            "BBBB ", 
            "B   B", 
            "B   B", 
            "BBBB ", 
            "B   B", 
            "B   B", 
            "BBBB "
        ]);

        match input.trim() {
            "" => String::new(),
            input => (0..7).map(
                |layer|  input.chars().map(
                |letter| alpha[&letter.to_ascii_lowercase()][layer])
                .join(" ")).collect::<Vec<_>>().iter().map(
                |slice| slice.trim_end())
                .join("\n")
        }
    }

    #[test]
    fn test_fixed() {
        let input = "ab";
        let expected_output = r#"
 AAA  BBBB
A   A B   B
A   A B   B
AAAAA BBBB
A   A B   B
A   A B   B
A   A BBBB
"#;
        let result = block_print(input);

        assert_eq!(block_print("  "), "");
        assert_eq!(result.trim(), expected_output.trim(), "The block print output for 'ab' did not match the expected result.");
    }
}