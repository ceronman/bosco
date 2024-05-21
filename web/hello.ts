const memory = new WebAssembly.Memory({ initial: 1 });

function print(offset: number, length: number) {
    const bytes = new Uint8Array(memory.buffer, offset, length);
    const string = new TextDecoder("utf8").decode(bytes);
    console.log(string);
}

const importObject = {
    "js": {
        "mem": memory,
        "print": print
    },
};

// @ts-ignore
let file = await Deno.readFile("hello.wasm");
let module = new WebAssembly.Module(file);
let instance = new WebAssembly.Instance(module, importObject);
// @ts-ignore
instance.exports.hello();
