type info =
  { data : int
  ; headers : int
  ; depth : int
  }

let objsize obj = { data = 0; headers = 0; depth = 0; }

let size_with_headers i = 0

let size_without_headers i = 0
