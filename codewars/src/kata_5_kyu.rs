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
    fn zoom(_n: i32) -> String {
        todo!()
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