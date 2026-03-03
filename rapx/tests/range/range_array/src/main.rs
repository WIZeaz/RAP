// fn method_for_loop() {
//     let mut read_element = 0;
//     let mut a = [0; 10];
//     for i in 0..a.len() {
//         read_element = a[i];

//         a[i] = i as i32;

//     }
//     // println!("method_for_loop: {:?}", a);
// }
fn method_for_slice_loop() {
    let mut a = [0; 10];
    let slice_index = 5;
    let slice = &mut a[1..slice_index];
    for i in 0..slice.len() {
        slice[i] = i+1 ;
    }
    // println!("method_for_loop: {:?}", a);
}
// fn method_for_loop_box() {
//     let mut a: Box<[i32; 10]> = Box::new([0; 10]);

//     for i in 0..a.len() {
//         a[i] = i as i32;
//     }

//     // println!("Box<[i32; 10]> on heap: {:?}", a);
// }
// fn method_iter_mut_enumerate() {
//     let mut a = [0; 10];
//     for (i, x) in a.iter_mut().enumerate() {
//         *x = i as i32;
//     }
//     // println!("method_iter_mut_enumerate: {:?}", a);
// }

// fn method_map_collect() {
//     let a: Vec<i32> = (0..10).map(|i| i).collect();
//     // println!("method_map_collect: {:?}", a);
// }

// // fn method_from_fn() {
// //     let a: Vec<i32> = std::iter::from_fn({
// //         let mut i = 0;
// //         Some(move || {
// //             if i < 10 {
// //                 let v = i;
// //                 i += 1;
// //                 Some(v)
// //             } else {
// //                 None
// //             }
// //         })
// //     })
// //     .collect();

// //     // println!("method_from_fn: {:?}", a);
// // }

// fn method_array_from_fn() {
//     let a = std::array::from_fn::<_, 10, _>(|i| i as i32);
//     // println!("method_array_from_fn: {:?}", a);
// }

// fn method_while_loop() {
//     let mut a = [0; 10];
//     let mut i = 0;
//     while i < a.len() {
//         a[i] = i as i32;
//         i += 1;
//     }
//     // println!("method_while_loop: {:?}", a);
// }

// fn method_unsafe_ptr() {
//     let mut a = [0; 10];
//     let ptr = a.as_mut_ptr();
//     for i in 0..a.len() {
//         unsafe { *ptr.add(i) = i as i32; }
//     }
//     // println!("method_unsafe_ptr: {:?}", a);
// }

fn main() {
    method_for_slice_loop();
    // method_iter_mut_enumerate();
    // method_map_collect();
    // method_from_fn();
    // method_array_from_fn();
    // method_while_loop();
    // method_unsafe_ptr();
}
