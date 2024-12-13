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