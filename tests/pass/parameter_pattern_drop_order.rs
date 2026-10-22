struct D(&'static str);

impl Drop for D {
    fn drop(&mut self) {
        println!("{}", self.0);
    }
}

impl D {
    fn method(self, (_x, _): (D, D), (_, _y): (D, D)) {
        println!("method");
    }
}

fn f((_x, _): (D, D), (_, _y): (D, D)) {
    println!("function");
}

fn mixed(_plain: D, (ref _borrowed, _): (D, D), (_, _owned): (D, D), _last: D) {
    println!("mixed");
}

fn main() {
    f((D("0"), D("1")), (D("2"), D("3")));
    let c = |(_x, _): (D, D), (_, _y): (D, D)| {
        println!("closure");
    };
    c((D("0"), D("1")), (D("2"), D("3")));
    D("self").method((D("0"), D("1")), (D("2"), D("3")));
    let cap = D("capture");
    let token = D("consumed");
    let once = move |(_x, _): (D, D), (_, _y): (D, D)| {
        println!("once {}", cap.0);
        drop(token);
    };
    once((D("0"), D("1")), (D("2"), D("3")));
    mixed(D("plain"), (D("borrowed"), D("rest")), (D("remainder"), D("owned")), D("last"));
}
