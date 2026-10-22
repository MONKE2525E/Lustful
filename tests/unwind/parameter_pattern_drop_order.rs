struct D(&'static str);

impl Drop for D {
    fn drop(&mut self) {
        println!("{}", self.0);
        if self.0 == "panic" {
            panic!("destructor cleanup");
        }
    }
}

fn f((_x, _): (D, D), (_, _y): (D, D)) {
    panic!("parameter cleanup");
}

fn returns((_x, _): (D, D), (_, _y): (D, D)) {}

impl D {
    fn method(self, (_x, _): (D, D), (_, _y): (D, D)) {
        panic!("method cleanup");
    }
}

fn main() {
    std::panic::set_hook(Box::new(|_| {}));
    let r = std::panic::catch_unwind(|| {
        f((D("0"), D("1")), (D("2"), D("3")));
    });
    println!("function caught {}", r.is_err());
    let r = std::panic::catch_unwind(|| {
        let c = |(_x, _): (D, D), (_, _y): (D, D)| {
            panic!("closure cleanup");
        };
        c((D("0"), D("1")), (D("2"), D("3")));
    });
    println!("closure caught {}", r.is_err());
    let r = std::panic::catch_unwind(|| {
        D("self").method((D("0"), D("1")), (D("2"), D("3")));
    });
    println!("method caught {}", r.is_err());
    let r = std::panic::catch_unwind(|| {
        let cap = D("capture");
        let token = D("consumed");
        let once = move |(_x, _): (D, D), (_, _y): (D, D)| {
            println!("once {}", cap.0);
            drop(token);
            panic!("once cleanup");
        };
        once((D("0"), D("1")), (D("2"), D("3")));
    });
    println!("once caught {}", r.is_err());
    let r = std::panic::catch_unwind(|| {
        returns((D("0"), D("1")), (D("2"), D("panic")));
    });
    println!("destructor caught {}", r.is_err());
}
