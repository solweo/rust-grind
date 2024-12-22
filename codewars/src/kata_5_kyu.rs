/// -*- coding:utf-8 -*-
/// title       : ■□ Pattern □■ : Zoom
/// kata UUID   : 56e6705b715e72fef0000647
/// tags        : ['ASCII Art', 'Puzzles']
/// ---------------------------------------------------
/// description : solutions for codewars.com
/// author      : solweo
/// -----------------------------------------------------
#[allow(dead_code)]
mod pattern_zoom {
    use itertools::Itertools;
    use std::cmp::max;

    fn zoom(n: i32) -> String {
        const EMPTY: char = '□';
        const FILLED: char = '■';

        let rule = |x: i32, y: i32| max(
            x.abs_diff(n/2), 
            y.abs_diff(n/2)) % 2 == 0;
        
        (0..n).map(|row| (0..n).map(|column| 
            match rule(row, column) {
                true => FILLED,
                false => EMPTY,
            })
            .join(""))
            .join("\n")
    }

    #[test]
    fn basic_test_1() {
    assert_eq!(zoom(1), "■");
    }

    #[test]
    fn basic_test_2() {
    assert_eq!(zoom(3), "\
□□□
□■□
□□□"
    );
    }

    #[test]
    fn basic_test_3() {
    assert_eq!(zoom(5), "\
■■■■■
■□□□■
■□■□■
■□□□■
■■■■■"
    );
    }

    #[test]
    fn basic_test_4() {
    assert_eq!(zoom(7), "\
□□□□□□□
□■■■■■□
□■□□□■□
□■□■□■□
□■□□□■□
□■■■■■□
□□□□□□□"
    );
    }

    #[test]
    fn basic_test_5() {
    assert_eq!(zoom(9), "\
■■■■■■■■■
■□□□□□□□■
■□■■■■■□■
■□■□□□■□■
■□■□■□■□■
■□■□□□■□■
■□■■■■■□■
■□□□□□□□■
■■■■■■■■■"
    );
    }
}

/// -*- coding:utf-8 -*-
/// title       : Find the smallest
/// kata UUID   : 573992c724fc289553000e95
/// tags        : ['Fundamentals']
/// ---------------------------------------------------
/// description : solutions for codewars.com
/// author      : solweo
/// -----------------------------------------------------
#[allow(dead_code)]
mod find_the_smallest {
    use itertools::Itertools;
    use std::cmp::Ordering;
    
    /// Solution without Brute-force
    fn smallest(n: i64) -> (i64, usize, usize) {
        let n = digits(n);

        // Regardless of the answer, the location of the change will be identical in all scenarios
        let place_of_change = n.iter().zip(n.iter().sorted())
            .position(|(original, shifted)| original != shifted)
            .unwrap_or(0);

        // But the thing is, we can't really tell whether the value was taken from that place or placed upon it
        // Therefore, it is vital to check both scenarios
        let try_from_right = n[place_of_change+1..]
            .iter()
            .rev()
            .tuple_windows()
            .scan(n.len()-1, |state, (&a, &b)|{
                if a == *n[place_of_change+1..].iter().min().unwrap() && a != b {
                    None
                } else {
                    *state -= 1;
                    Some(*state)
                }
            }).last().unwrap_or(n.len()-1);

        let try_to_right = n[place_of_change+1..]
            .iter()
            .tuple_windows()
            .scan(place_of_change+1, |state, (_, &b)|{
                if b > n[place_of_change] {
                    None
                } else {
                    *state += 1;
                    Some(*state)
                }
            }).last().unwrap_or(place_of_change+1);

        // There is an chance of getting a raw of exect same digits which sadly aren't ancounetred
        let try_to_right = n[place_of_change+1..=try_to_right].iter()
            .rposition(|&digit| digit != n[place_of_change])
            .map_or(try_to_right, |pos| place_of_change + 1 + pos);
        let place_of_change = n[0..place_of_change].iter()
            .position(|&digit| digit == n[try_from_right])
            .unwrap_or(place_of_change);

        // Generate possible moves and evaluate them
        let moves = [
            move_digit(&mut n.clone(), try_from_right, place_of_change),
            move_digit(&mut n.clone(), place_of_change, try_to_right),
        ];

        // Return the smallest result
        *moves
            .iter()
            .min_by(|&(num1, i1, j1), &(num2, i2, j2)| {
                match num1.cmp(num2) {
                    Ordering::Equal => match i1.cmp(i2) {
                        Ordering::Equal => j1.cmp(j2),
                        x => x,
                    },
                    x => x,
                }
            }) 
            .unwrap()
    }

    fn digits(n: i64) -> Vec<u8> {
        let mut digits = std::iter::repeat(())
            .scan(n, |i, _dummy_value| {
                if *i > 0 {
                    let digit = (*i % 10) as u8;
                    *i /= 10;
                    Some(digit)
                } else {
                    None
                }
            }).collect::<Vec<_>>();

        digits.reverse();
        digits
    }
    
    fn from_digits(digits: &[u8]) -> i64 {
        digits.iter().fold(0i64, |acc, &digit| acc * 10 + digit as i64)
    }
    
    fn move_digit(digits: &mut Vec<u8>, i: usize, j: usize) -> (i64, usize, usize) {
        if i != j {
            let digit = digits.remove(i);
            digits.insert(j, digit);
        }

        (from_digits(digits), i, j)
    }

    fn testing(n: i64, exp: (i64, usize, usize)) {
        let ans = smallest(n);
        assert_eq!(ans, exp, "Testing: {}", n);
    }

    #[test]
    fn basic_tests() {
        testing(209917, (29917, 0, 1));
        testing(269045, (26945, 3, 0));  
        testing(285365, (238565, 3, 1)); 
        testing(261235, (126235, 2, 0));
        testing(219957, (129957, 0, 1));
        testing(935855753, (358557539, 0, 8)); 
        testing(199819884756, (119989884756, 4, 0)); 
        testing(11199819884756, (11119989884756, 6, 0));  
        testing(223399839884756, (223339989884756, 7, 2));  
        testing(29979573762081003, (2997957376208103, 14, 0)); 
        testing(524496252664355423, (244596252664355423, 0, 3)); 
        testing(755566437707740963, (75556643770774963, 14, 0));  
        testing(905537475245977679, (55374752459776799, 0, 16));       
        testing(404701664395569970, (40470166439556997, 17, 0));
        testing(901246778163629482, (12467781636294829, 0, 17));
        testing(603613412202040716, (36134122020406716, 0, 14));
        testing(837687834358978897, (376878343588978897, 0, 10));
    }
}