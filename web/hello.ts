const memory = new WebAssembly.Memory({ initial: 1 });

function print(offset: number, length: number) {
    const bytes = new Uint8Array(memory.buffer, offset, length);
    const string = new TextDecoder("utf8").decode(bytes);
    console.log(string);
}

function print_num(number: number) {
    console.log(number)
}

const importObject = {
    "js": {
        "mem": memory,
        "print": print,
        "print_num": print_num
    },
};

// @ts-ignore
let file = await Deno.readFile("hello.wasm");
let module = new WebAssembly.Module(file);
let instance = new WebAssembly.Instance(module, importObject);

console.log("Starting...")

// @ts-ignore
instance.exports.hello();
