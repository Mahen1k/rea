import { expect, it } from "vitest";
import { analyzeJavaScriptSemantics } from "./javascriptSemanticAnalysis.js";

it.each([
  "box.owner=1;",
  "box.owner={nested:1};",
  "const value={nested:1}; box.owner=value;",
  "const alias=box; alias.owner=1;",
  "box.child={owner:1};",
  "box.owner=box;",
  "box.owner ||= 1;",
  "Reflect.set(box,'owner',1);",
  "Reflect.set.call(null,box,'owner',1);",
  "Object.assign(box,{owner:1});",
  "Object.assign(box,{owner:{nested:1}});",
  "Object.defineProperty(box,'owner',{value:1});",
  "Reflect.defineProperty(box,'owner',{value:1});",
  "Object.defineProperties(box,{owner:{value:1}});",
])("keeps module-free values written to local properties: %s", (write) => {
  expect(
    analyzeJavaScriptSemantics(`const box={}; ${write}
      Object.assign=custom; Object.assign({},box.owner,box.child);
      require('fs').readFileSync('kept');`).configurationOperations.map(
      ({ key }) => key,
    ),
  ).toEqual(["kept"]);
});

it.each([
  "const value={owner:module}; box.owner=value;",
  "const value={}; box.owner=value; value.owner=module;",
  "box.child={owner:module};",
  "box.owner=box; box.child=module;",
  "box.owner ||= module;",
  "Object.assign(box,{owner:1},{owner:module});",
  "Object.defineProperties(box,{owner:{value:1},owner:{value:module}});",
  "Object.defineProperties(box,{owner:{value:1},[key]:{value:module}});",
  "Object.defineProperty(box,'owner',{get(){return module;}});",
  "Object.assign(box,{get owner(){return module;}});",
  "function getOwner(){return module;} box.owner=getOwner();",
  "box.owner=()=>module;",
  "box.owner=unknown;",
])(
  "retains module-bearing values through local property writes: %s",
  (write) => {
    expect(
      analyzeJavaScriptSemantics(`const box={}; ${write}
      Object.assign=custom; Object.assign({},box.owner,box.child);
      require('fs').readFileSync('wrong');`).configurationOperations,
    ).toEqual([]);
  },
);

it.each([
  "Object.defineProperty(fs,'statSync',{set(v){this.cp.spawn=custom;}});",
  "Reflect.defineProperty(fs,'statSync',{set(v){this.cp.spawn=custom;}});",
  "Object.defineProperties(fs,{statSync:{set(v){this.cp.spawn=custom;}}});",
  "const alias=fs; Object.defineProperty(alias,'statSync',{set(v){this.cp.spawn=custom;}});",
  "configure(fs);",
])("revisits deferred Reflect descriptor proof: %s", (install) => {
  const ir = analyzeJavaScriptSemantics(`const cp=require('child_process');
    const fs=require('fs');
    function run(){Reflect.set(fs,'statSync',1,{cp}); cp.spawn('wrong');}
    ${install} run();`);
  expect(ir.childProcessSpawns).toEqual([]);
});

it.each([
  "Reflect.set.call(null,fs,'statSync',1,{cp});",
  "Reflect.set.apply(null,[fs,'statSync',1,{cp}]);",
  "const set=Reflect.set; set(fs,'statSync',1,{cp});",
])("retains deferred descriptor effects through %s", (invoke) => {
  expect(
    analyzeJavaScriptSemantics(`const cp=require('child_process');
    const fs=require('fs'); const run=()=>{${invoke} cp.spawn('wrong');};
    Object.defineProperty(fs,'statSync',{set(v){this.cp.spawn=custom;}});
    run();`).childProcessSpawns,
  ).toEqual([]);
});

it.each([
  "Reflect.set(fs,'statSync',1,{cp}); cp.spawn('kept'); Object.defineProperty(fs,'statSync',{set(v){this.cp.spawn=custom;}});",
  "function run(){Reflect.set(fs,'statSync',1,{cp}); cp.spawn('kept');} Object.defineProperty(fs,'unrelated',{set(v){this.cp.spawn=custom;}}); run();",
  "function run(){Reflect.set(fs,'statSync',1,{cp}); cp.spawn('kept');} run();",
])("preserves independently proven Reflect data writes: %s", (body) => {
  expect(
    analyzeJavaScriptSemantics(`const cp=require('child_process');
    const fs=require('fs'); ${body}`).childProcessSpawns.map(
      ({ method }) => method,
    ),
  ).toEqual(["spawn"]);
});

it.each([
  "box.owner=module;",
  "const alias=box; alias.owner=module;",
  "box['owner']=module;",
  "box[key]=module;",
  "Reflect.set(box,'owner',module);",
  "Object.defineProperty(box,'owner',{value:module});",
  "Object.defineProperties(box,{owner:{value:module}});",
  "Object.assign(box,{owner:module});",
])("retains wrapper exposure through written local properties: %s", (write) => {
  expect(
    analyzeJavaScriptSemantics(`const box={}; ${write}
    Object.assign=(target,value)=>{value.require=replacement};
    Object.assign({},box.owner); require('fs').readFileSync('wrong');
  `).configurationOperations,
  ).toEqual([]);
});

it.each([
  "const box={}; const saved=box; box.owner=module; Object.assign({},saved.owner);",
  "const box={}; function run(){Object.assign({},box.owner);} box.owner=module; run();",
  "const box={child:{}}; box.child.owner=module; Object.assign({},box.child);",
  "const box={}; Object.assign({},box.owner); box.owner=module; Object.assign({},box.owner);",
])("retains shared local object exposure at its use: %s", (body) => {
  expect(
    analyzeJavaScriptSemantics(`Object.assign=(target,value)=>{(value.owner ?? value).require=replacement};
    ${body} require('fs').readFileSync('wrong');`).configurationOperations,
  ).toEqual([]);
});

it.each([
  "const box={owner:{}}; box.other=module; Object.assign({},box.owner); require('fs').readFileSync('kept');",
  "const box={owner:{}}; Object.assign({},box.owner); require('fs').readFileSync('kept'); box.owner=module;",
  "const box={owner:{}}; const saved=box.owner; box.owner=module; Object.assign({},saved); require('fs').readFileSync('kept');",
])("keeps written local exposure scoped to the read: %s", (body) => {
  expect(
    analyzeJavaScriptSemantics(`Object.assign=(target,value)=>{value.require=replacement};
    ${body}`).configurationOperations.map(({ key }) => key),
  ).toEqual(["kept"]);
});

const intrinsicReplacementForms = [
  "Object.defineProperty(Reflect,'set',{value:bound});",
  "Reflect.defineProperty(Reflect,'set',{value:bound});",
  "Object.defineProperties(Reflect,{set:{value:bound}});",
  "Object.assign(Reflect,{set:bound});",
  "Reflect.set(Reflect,'set',bound);",
  "Object.defineProperty.call(null,Reflect,'set',{value:bound});",
  "Object.assign.apply(null,[Reflect,{set:bound}]);",
  "const descriptor={value:bound}; Object.defineProperty(Reflect,'set',descriptor);",
  "const properties={set:bound}; Object.assign(Reflect,properties);",
];

it.each(intrinsicReplacementForms)(
  "follows native intrinsic replacement values: %s",
  (replace) => {
    for (const receiver of ["module", "{}"])
      expect(
        analyzeJavaScriptSemantics(`const bound=Reflect.set.bind(null,${receiver});
          ${replace} Reflect.set('require',replacement);
          require('fs').readFileSync('kept');`).configurationOperations.map(
          ({ key }) => key,
        ),
      ).toEqual(receiver === "module" ? [] : ["kept"]);
  },
);

it.each([
  "Object.assign(Reflect,{other:bound});",
  "Object.defineProperties(Reflect,{other:{value:bound}});",
  "Object.defineProperty(Reflect,'other',{value:bound});",
  "Reflect.set(Reflect,'set',bound,{});",
])("keeps native intrinsic replacement slots distinct: %s", (replace) => {
  expect(
    analyzeJavaScriptSemantics(`const bound=Reflect.set.bind(null,module);
      ${replace} Reflect.set({},'require',replacement);
      require('fs').readFileSync('kept');`).configurationOperations.map(
      ({ key }) => key,
    ),
  ).toEqual(["kept"]);
});

it.each(intrinsicReplacementForms)(
  "keeps reads before native intrinsic replacement: %s",
  (replace) => {
    expect(
      analyzeJavaScriptSemantics(`const bound=Reflect.set.bind(null,module);
        Reflect.set({},'require',replacement); require('fs').readFileSync('kept');
        ${replace}`).configurationOperations.map(({ key }) => key),
    ).toEqual(["kept"]);
  },
);

it.each([
  "Reflect.set(module);",
  "Reflect.set.call(null,module);",
  "Reflect.set.apply(null,[module]);",
  "const set=Reflect.set.bind(null,module); set();",
  "Reflect.set(module,'require',replacement,require('node:path'));",
  "const path=require('node:path'); Reflect.set(module,'require',replacement,path);",
  "import path from 'node:path'; Reflect.set(module,'require',replacement,path);",
  "Reflect.set(module,'require',replacement,require('node:util'));",
  "Reflect.set(module,'require',replacement,new (class {})());",
  "class Receiver{} Reflect.set(module,'require',replacement,new Receiver());",
  "function Receiver(){} Reflect.set(module,'require',replacement,new Receiver());",
  "const Receiver=function(){}; Reflect.set(module,'require',replacement,new Receiver());",
  "Reflect.set(module,'require',replacement,new (class {constructor(){return 1;}})());",
  "Reflect.set(module,'require',replacement,new (function(){return this;})());",
])(
  "keeps the wrapper loader for distinct receivers or omitted keys: %s",
  (setup) => {
    expect(
      analyzeJavaScriptSemantics(
        `${setup} require('fs').readFileSync('kept');`,
      ).configurationOperations.map(({ key }) => key),
    ).toEqual(["kept"]);
  },
);

it.each([
  "Reflect.set(module,key,replacement);",
  "Reflect.set(...args);",
  "Reflect.set(module,'require',replacement,require('external'));",
  "Reflect.set(module,'require',replacement,require('node:path').owner);",
  "Reflect.set(module,'require',replacement,new (class {constructor(){return module;}})());",
  "Reflect.set(module,'require',replacement,new (function(){return module;})());",
  "Reflect.set(module,'require',replacement,new (class extends Base {})());",
  "Reflect.set(module,'require',replacement,new (class {constructor(){if(flag)return module;}})());",
  "let Receiver=class {}; Receiver=custom; Reflect.set(module,'require',replacement,new Receiver());",
  "Object.assign=custom; const box={safe:{id:1},owner:module}; Object.assign({},box.safe); Object.assign({},box.owner);",
  "Object.assign=custom; const box={safe:{id:1},owner:module}; Object.assign({},box.safe); Object.assign({},box);",
  "Object.assign=custom; let payload={id:1}; Object.assign({},payload); payload={owner:module}; Object.assign({},payload);",
])(
  "retains uncertainty after cached projections or unknown construction: %s",
  (setup) => {
    expect(
      analyzeJavaScriptSemantics(
        `${setup} require('fs').readFileSync('wrong');`,
      ).configurationOperations,
    ).toEqual([]);
  },
);

it.each([
  "let fs={}; outer:{ if(flag) break outer; fs=require('fs'); } fs.readFileSync('wrong');",
  "let fs={}; outer:{{ if(flag) break outer; fs=require('fs'); }} fs.readFileSync('wrong');",
  "let fs={}; outer:{ inner:{if(flag) break outer;} fs=require('fs');} fs.readFileSync('wrong');",
  "function run(){const r=Object.create(null); Reflect.set(r,'require',replacement); require('fs').readFileSync('wrong');} Object.create=()=>module; run();",
  "const run=()=>{const r=Object.create(null); Reflect.set(r,'require',replacement); require('fs').readFileSync('wrong');}; Object.create=()=>module; run();",
  "class C{value=(()=>{const r=Object.create(null); Reflect.set(r,'require',replacement); require('fs').readFileSync('wrong');})();} Object.create=()=>module; new C();",
  "while(flag){const r=Object.create(null); Reflect.set(r,'require',replacement); require('fs').readFileSync('wrong'); Object.create=()=>module;}",
  "function run(){const fs=require('fs'); Reflect.set(fs,'readFileSync',custom,{}); fs.readFileSync('wrong');} Reflect.set=(target,key,value)=>{target[key]=value}; run();",
])(
  "does not order skipped or repeated/deferred writes as definite: %s",
  (source) => {
    expect(analyzeJavaScriptSemantics(source).configurationOperations).toEqual(
      [],
    );
  },
);

it.each([
  "let fs=require('fs'); fs.readFileSync('kept'); outer:{if(flag)break outer; fs={};}",
  "function run(){const r=Object.create(null); Reflect.set(r,'require',replacement); require('fs').readFileSync('kept');} run();",
])(
  "keeps independently proven reads across control-flow barriers: %s",
  (source) => {
    expect(
      analyzeJavaScriptSemantics(source).configurationOperations.map(
        ({ key }) => key,
      ),
    ).toEqual(["kept"]);
  },
);

it.each([
  "const {id}=module; Object.assign=custom; Object.assign({},id);",
  "const {filename:name}=module; const alias=name; Object.assign=custom; Object.assign({},alias);",
  "const {id}=module; Reflect.set=custom; Reflect.set({},'x',id);",
  "Reflect.set=custom; Reflect.set({},'x',1);",
  "Reflect.set=custom; Reflect.set.call(null,{},'x',1);",
  "Reflect.set=custom; Reflect.set.apply(null,[{},'x',1]);",
  "Reflect.set=custom; const set=Reflect.set.bind(null,{},'x'); set(1);",
  "const r=Object.create(null); Object.create=custom; Reflect.set(module,'require',replacement,r);",
])(
  "keeps module-free opaque arguments and prior allocations separate: %s",
  (setup) => {
    expect(
      analyzeJavaScriptSemantics(
        `${setup} require('fs').readFileSync('kept');`,
      ).configurationOperations.map(({ key }) => key),
    ).toEqual(["kept"]);
  },
);

it.each([
  "module.id=module; const {id}=module; Object.assign=custom; Object.assign({},id);",
  "Object.assign=custom; const box={id:'text',owner:module}; const {id,owner}=box; Object.assign({},owner,id);",
  "Object.assign=custom; const {owner}={owner:module}; Object.assign({},owner);",
  "Object.assign=custom; const [owner]=[module]; Object.assign({},owner);",
  "Object.assign=custom; const {box:{owner}}={box:{owner:module}}; Object.assign({},owner);",
  "Reflect.set=custom; Reflect.set(module,'require',replacement);",
  "Reflect.set=custom; Reflect.set({},'x',{owner:module});",
  "Reflect.set=custom; const set=Reflect.set.bind(null,module); set('require',replacement);",
  "Object.create=custom; const r=Object.create(null); Reflect.set(module,'require',replacement,r);",
])(
  "retains wrapper exposure through projected and opaque arguments: %s",
  (setup) => {
    expect(
      analyzeJavaScriptSemantics(
        `${setup} require('fs').readFileSync('wrong');`,
      ).configurationOperations,
    ).toEqual([]);
  },
);

it.each([
  "const fs=require('fs'); Reflect.set(fs,'readFileSync',custom,{}); fs.readFileSync('kept'); Reflect.set=other;",
  "const fs=require('fs'); Reflect.set(fs,'readFileSync',custom,{}); Reflect.set=other; fs.readFileSync('kept');",
])("orders the Reflect intrinsic proof at invocation: %s", (source) => {
  expect(
    analyzeJavaScriptSemantics(source).configurationOperations.map(
      ({ key }) => key,
    ),
  ).toEqual(["kept"]);
});

it.each([
  "const proc=require('process'); Reflect.set(proc,'env',{},{}); const mode=proc.env.MODE;",
  "const proc=require('node:process'); Reflect.set(proc,'argv',[],{}); const mode=proc.env.MODE;",
])("honors explicit receivers for native process data slots: %s", (source) => {
  expect(
    analyzeJavaScriptSemantics(source).configurationOperations.map(
      ({ key }) => key,
    ),
  ).toEqual(["MODE"]);
});

it.each([
  "Reflect.set(proc,'env',{});",
  "Object.defineProperty(proc,'env',{set(value){this.proc.env={};}}); Reflect.set(proc,'env',{}, {proc});",
])("retains changed process descriptor effects: %s", (setup) => {
  expect(
    analyzeJavaScriptSemantics(
      `const proc=require('process'); ${setup} const mode=proc.env.MODE;`,
    ).configurationOperations,
  ).toEqual([]);
});

it.each([
  "const {promises:fsp}=require('fs'); patch(require('fs/promises'));",
  "const fsp=require('fs').promises; patch(require('fs/promises'));",
  "const {promises:fsp}=require('fs'); patch(require('fs'));",
  "const {promises:fsp}=require('fs'); patch(fsp);",
])("keeps escapes of saved objects effective: %s", (setup) => {
  expect(
    analyzeJavaScriptSemantics(`${setup} const h=fsp.open('wrong'); h.close();`)
      .resourceOperations,
  ).toEqual([]);
});

it.each([
  "Reflect.set(Object.create(null),'hook',1,{fs});",
  "const target=Object.create(null); Reflect.set(target,'hook',1,{fs});",
  "const target={__proto__:null}; Reflect.set(target,'hook',1,{fs});",
  "const target=Object.create(null); const alias=target; Reflect.set(alias,'hook',1,{fs});",
  "Object.defineProperty(Object.prototype,'statSync',{set(){this.readFileSync=custom;}}); Reflect.set(fs,'statSync',custom);",
  "fs.statSync('probe'); Reflect.set(fs,'readFileSync',custom,{});",
  "const target=Object.create(null); Reflect.set(target,'hook',1,{fs}); Reflect.set(target,'hook',2,{fs});",
])("preserves reads when the selected setter cannot run: %s", (setup) => {
  expect(
    analyzeJavaScriptSemantics(
      `const fs=require('fs'); ${setup} fs.readFileSync('kept');`,
    ).configurationOperations.map(({ key }) => key),
  ).toEqual(["kept"]);
});

it.each([
  "delete fs.statSync; Object.defineProperty(Object.prototype,'statSync',{set(){this.readFileSync=custom;}}); Reflect.set(fs,'statSync',custom);",
  "delete require('fs').statSync; Object.defineProperty(Object.prototype,'statSync',{set(){this.readFileSync=custom;}}); Reflect.set(fs,'statSync',custom);",
  "const target=Object.create(null,{hook:{set(){this.fs.readFileSync=custom;}}}); Reflect.set(target,'hook',1,{fs});",
  "const target=Object.create(null); Object.defineProperty(target,'hook',{set(){this.fs.readFileSync=custom;}}); Reflect.set(target,'hook',1,{fs});",
  "Object.create=()=>({set hook(v){this.fs.readFileSync=custom;}}); Reflect.set(Object.create(null),'hook',1,{fs});",
  "const target=Object.create(null); const alias=target; Object.defineProperty(alias,'hook',{set(){this.fs.readFileSync=custom;}}); Reflect.set(target,'hook',1,{fs});",
])("rechecks descriptors before excluding setter effects: %s", (setup) => {
  expect(
    analyzeJavaScriptSemantics(
      `const fs=require('fs'); ${setup} fs.readFileSync('wrong');`,
    ).configurationOperations,
  ).toEqual([]);
});

it.each([
  "let fs=require('fs'); fs.readFileSync('kept'); {fs={};}",
  "let fs=require('fs'); fs.readFileSync('kept'); {{{fs={};}}}",
  "let fs=require('fs'); {fs.readFileSync('kept'); {fs={};}}",
  "let fs; {fs=require('fs');} fs.readFileSync('kept');",
  "let fs={}; {fs=require('fs');} fs.readFileSync('kept');",
  "let fs=require('fs'); fs.readFileSync('kept'); if(flag){fs={};}",
])("retains reads before later nested initializers: %s", (source) => {
  expect(
    analyzeJavaScriptSemantics(source).configurationOperations.map(
      ({ key }) => key,
    ),
  ).toEqual(["kept"]);
});

it.each([
  "let fs=require('fs'); if(flag){fs={};} fs.readFileSync('wrong');",
  "let fs; if(flag){fs=require('fs');} fs.readFileSync('wrong');",
  "let fs=require('fs'); function later(){fs={};} fs.readFileSync('wrong');",
])(
  "keeps conditional and deferred initializer projection conservative: %s",
  (source) => {
    expect(analyzeJavaScriptSemantics(source).configurationOperations).toEqual(
      [],
    );
  },
);

it.each([
  "Object.assign=(target,source)=>{target.require=source.require;}; Object.assign(module,{require:replacement});",
  "Object.defineProperty=(target,key,descriptor)=>{target[key]=descriptor.value;}; Object.defineProperty(module,'require',{value:replacement});",
  "Object.defineProperties=(target,descriptors)=>{target.require=descriptors.require.value;}; Object.defineProperties(module,{require:{value:replacement}});",
  "Object.assign=(target,source)=>{target.require=source.require;}; Object.assign.call(null,module,{require:replacement});",
  "Object.assign=(target,source)=>{target.require=source.require;}; Object.assign.apply(null,[module,{require:replacement}]);",
  "const owner=module; Object.assign=custom; Object.assign(owner,{require:replacement});",
  "Object.assign=custom; const args=[module,{require:replacement}]; Object.assign.apply(null,args);",
  "Object.assign=custom; const patch=Object.assign.bind(null,module); patch({require:replacement});",
])(
  "retains delegate invalidation through opaque Object mutators: %s",
  (mutation) => {
    expect(
      analyzeJavaScriptSemantics(
        `${mutation} require('fs').readFileSync('wrong');`,
      ).configurationOperations,
    ).toEqual([]);
  },
);

it.each([
  "Object.assign(module, { [key]: replacement });",
  "Object.assign(module, { ...replacement });",
  "Object.assign(module, { require() {} });",
  "Object.defineProperties(module, { [key]: { value: replacement } });",
  "Reflect.set(module, 'require', replacement);",
  "Reflect.set(module, key, replacement);",
  "Reflect.set({}, 'require', replacement, module);",
  "const receiver=module; Reflect.set({}, 'require', replacement, receiver);",
  "Reflect.set(module, 'require', replacement, receiver);",
  "Reflect.set(module, 'require', replacement, ...receivers);",
  "Reflect.apply(Reflect.set, null, [{}, 'require', replacement, module]);",
  "const set=Reflect.set.bind(null, {}, 'require', replacement); set(module);",
  "Object.defineProperty(module, 'require', {value: replacement}, {});",
  "let owner=module; owner.require=replacement; owner={};",
  "Object.create=()=>module; const registry=Object.create(null); Reflect.set(registry, key, replacement);",
  "function Object(){}; Object.create=()=>module; Reflect.set(Object.create(null), key, replacement);",
  "const receiver=require('./local'); Reflect.set(receiver, 'require', replacement);",
  "let receiver=require('fs'); receiver=module; Reflect.set(receiver, 'require', replacement);",
  "Object.create.call=()=>module; const registry=Object.create.call(null,null); Reflect.set(registry,'require',replacement);",
  "Object.create.apply=()=>module; const registry=Object.create.apply(null,[null]); Reflect.set(registry,'require',replacement);",
  "Object.create.bind=()=>()=>module; const make=Object.create.bind(null,null); Reflect.set(make(),'require',replacement);",
])("invalidates the wrapper loader at its write: %s", (write) => {
  const ir = analyzeJavaScriptSemantics(`${write}
    const fs=require('fs'); fs.readFileSync('wrong');`);
  expect(ir.configurationOperations).toEqual([]);
});

it.each([
  "Object.assign(module, { unrelated: replacement });",
  "Object.defineProperties(module, { unrelated: { value: replacement } });",
  "Reflect.set(module, 'unrelated', replacement);",
  "const registry=Object.create(null); Reflect.set(registry, key, replacement);",
  "const registry=Object.create(module); Reflect.set(registry, 'require', replacement);",
  "const fs=require('node:fs'); Reflect.set(fs, 'require', replacement);",
  "const fs=require('fs'); const receiver=fs; Reflect.set(module, 'require', replacement, receiver);",
  "import * as fs from 'node:fs'; Reflect.set(fs, 'require', replacement);",
  "let receiver=module; receiver=require('fs'); Reflect.set(receiver, 'require', replacement);",
  "Reflect.set(module, 0, replacement);",
  "Reflect.set(module, -0, replacement);",
  "Reflect.set(module, true, replacement);",
  "Reflect.set(module, null, replacement);",
  "Reflect.set(module, undefined, replacement);",
  "Reflect.set(module, void 0, replacement);",
  "Reflect.set(module, 1n, replacement);",
  "const key=0; Reflect.set(module, key, replacement);",
  "Reflect.set(module, 'require', replacement, {});",
  "const receiver={}; Reflect.set(module, 'require', replacement, receiver);",
  "Reflect.set(module, 'require', replacement, null);",
  "Reflect.set(module, 'require', replacement, undefined);",
  "Reflect.set(module, 'require', replacement, -1);",
  "Reflect.set(module, 'require', replacement, +value);",
  "Reflect.set(module, 'require', replacement, !value);",
  "Reflect.set(module, 'require', replacement, ~value);",
  "Reflect.set(module, 'require', replacement, typeof value);",
  "Reflect.apply(Reflect.set, null, [module, 'require', replacement, {}]);",
  "const set=Reflect.set.bind(null, module, 'require', replacement); set({});",
  "let owner=module; owner={}; owner.require=replacement;",
])("preserves the wrapper loader across unrelated writes: %s", (write) => {
  const ir = analyzeJavaScriptSemantics(`${write}
    require('fs').readFileSync('kept');`);
  expect(ir.configurationOperations.map(({ key }) => key)).toEqual(["kept"]);
});

it.each(["globalThis", "global", "self", "window"])(
  "recognizes an unchanged qualified process receiver: %s",
  (global) => {
    const ir = analyzeJavaScriptSemantics(`${global}.process.cwd();
      const proc=require('process'); const mode=proc.env.MODE;`);
    expect(ir.configurationOperations.map(({ key }) => key)).toEqual(["MODE"]);
  },
);

it.each([
  "let fs=require('fs'); fs.readFileSync('kept'); fs={};",
  "let read=require('fs').readFileSync; read('kept'); read=custom;",
  "let proc=require('process'); const mode=proc.env.kept; proc={};",
  "const fs=require('fs'); fs.readFileSync('kept'); if(flag) { fs.readFileSync=custom; }",
  "const fs=require('fs'); if(flag) { fs.readFileSync('kept'); } fs.readFileSync=custom;",
  "const fs=require('fs'); { fs.readFileSync('kept'); } if(flag) { fs.readFileSync=custom; }",
])("retains a builtin read before a later effect: %s", (source) => {
  const ir = analyzeJavaScriptSemantics(source);
  expect(ir.configurationOperations.map(({ key }) => key)).toEqual(["kept"]);
});

it.each([
  "const fs=require('fs'); if(flag) { fs.readFileSync=custom; } fs.readFileSync('wrong');",
  "const fs=require('fs'); function later() { fs.readFileSync('wrong'); } fs.readFileSync=custom;",
  "const fs=require('fs'); for(;;) { fs.readFileSync('wrong'); fs.readFileSync=custom; }",
  "const fs=require('fs'); class C { value=fs.readFileSync('wrong'); } fs.readFileSync=custom;",
])("keeps conditional and delayed writes conservative: %s", (source) => {
  expect(analyzeJavaScriptSemantics(source).configurationOperations).toEqual(
    [],
  );
});

it.each([
  "statSync",
  "readdirSync",
  "mkdirSync",
  "accessSync",
  "lstatSync",
  "realpathSync",
])("does not escape the namespace through native fs.%s", (method) => {
  const ir =
    analyzeJavaScriptSemantics(`const fs=require('fs'); fs.${method}('probe');
      fs.readFileSync('kept');`);
  expect(ir.configurationOperations.map(({ key }) => key)).toEqual(["kept"]);
});

it.each(["stat", "readdir", "mkdir"])(
  "does not escape the namespace through native promises.%s",
  (method) => {
    const ir =
      analyzeJavaScriptSemantics(`const fs=require('fs/promises'); fs.${method}('probe');
      fs.open('kept');`);
    expect(ir.resourceOperations.map(({ method }) => method)).toEqual(["open"]);
  },
);

// Public filesystem functions outside the original synchronous subset.
// Constructors and private exports are deliberately not receiver guarantees.
it.each([
  "exists",
  "glob",
  "globSync",
  "mkdtempDisposableSync",
  "openAsBlob",
  "watch",
  "watchFile",
  "unwatchFile",
  "createReadStream",
  "createWriteStream",
])("retains native fs reads after public fs.%s calls", (method) => {
  for (const specifier of ["fs", "node:fs"]) {
    const ir = analyzeJavaScriptSemantics(`const fs=require('${specifier}');
      fs.${method}('probe'); fs.readFileSync('kept');`);
    expect(ir.configurationOperations.map(({ key }) => key)).toContain("kept");
    const replaced =
      analyzeJavaScriptSemantics(`const fs=require('${specifier}');
      fs.${method}=custom; fs.${method}('probe'); fs.readFileSync('wrong');`);
    expect(replaced.configurationOperations).toEqual([]);
  }
});

it.each(["glob", "mkdtempDisposable", "lchmod", "watch"])(
  "retains native promises reads after public promises.%s calls",
  (method) => {
    for (const imported of [
      "const fs=require('node:fs/promises');",
      "const fs=require('fs').promises;",
      "import * as fs from 'node:fs/promises';",
    ]) {
      const ir = analyzeJavaScriptSemantics(
        `${imported} fs.${method}('probe'); fs.open('kept');`,
      );
      expect(ir.resourceOperations.map(({ method }) => method)).toContain(
        "open",
      );
    }
  },
);

it.each([";", ","])(
  "orders repeated writes and reads with %s separators",
  (separator) => {
    const keys = Array.from({ length: 64 }, (_, i) => `kept-${i}`);
    const operations = keys.map(
      (key) => `fs=require('fs'),fs.readFileSync('${key}'),fs={}`,
    );
    const ir = analyzeJavaScriptSemantics(
      `let fs; ${operations.join(separator)};`,
    );
    expect(ir.configurationOperations.map(({ key }) => key)).toEqual(keys);
  },
);

it.each([
  "let fs=require('fs'); fs=(fs.readFileSync('kept'),{}),fs.readFileSync('wrong');",
  "let fs; fs=require('fs'),fs={},fs.readFileSync('wrong');",
  "let fs=require('fs'); {fs={}; fs.readFileSync('wrong');}",
  "let fs=require('fs'); function later(){fs.readFileSync('wrong');} fs={};",
])("retains assignment completion and activation boundaries: %s", (source) => {
  expect(
    analyzeJavaScriptSemantics(source).configurationOperations.map(
      ({ key }) => key,
    ),
  ).toEqual(source.includes("'kept'") ? ["kept"] : []);
});

it("keeps a replaced native receiver uncertain", () => {
  const ir = analyzeJavaScriptSemantics(`const fs=require('fs');
    fs.statSync=custom; fs.statSync('probe'); fs.readFileSync('wrong');`);
  expect(ir.configurationOperations).toEqual([]);
});

it.each([
  "Reflect.set(fs, 'readFileSync', custom);",
  "Reflect.set(fs, key, custom);",
  "Reflect.set = custom; Reflect.set(fs, 'require', replacement);",
  "Object.defineProperty(fs, 'require', {set(value) {fs.readFileSync=custom;}}); Reflect.set(fs, 'require', replacement);",
  "Reflect.set.call=()=>{fs.readFileSync=custom}; Reflect.set.call(null, fs, 'require', replacement);",
  "Reflect.set.apply=()=>{fs.readFileSync=custom}; Reflect.set.apply(null, [fs, 'require', replacement]);",
  "const target={fs,set hook(value){this.fs.readFileSync=custom;}}; Reflect.set(target, 'hook', 1);",
  "const target={fs,set hook(value){this.fs.readFileSync=custom;}}; Reflect.set(target, key, 1);",
  "const target={set hook(value){this.fs.readFileSync=custom;}}; Reflect.set(target, 'hook', 1, {fs});",
])("keeps builtin mutations through Reflect.set conservative: %s", (write) => {
  expect(
    analyzeJavaScriptSemantics(
      `const fs=require('fs'); ${write} require('fs').readFileSync('wrong');`,
    ).configurationOperations,
  ).toEqual([]);
});

it.each(["process", "proc"])(
  "retains scalar process reads passed to calls: %s",
  (receiver) => {
    const ir = analyzeJavaScriptSemantics(`const proc=require('process');
    const port=Number(${receiver}.env.PORT); consume(${receiver}.argv[2]);`);
    expect(ir.configurationOperations.map(({ key }) => key)).toEqual([
      "PORT",
      "2",
    ]);
  },
);

it("tracks process writes through self-reassigned global aliases", () => {
  const ir =
    analyzeJavaScriptSemantics(`let host=globalThis; host=host.globalThis;
    host.process.env={}; const proc=require('process'); const value=proc.env.MODE;`);
  expect(ir.configurationOperations).toEqual([]);
});

it("retains each builtin read across repeated assignments and later writes", () => {
  const keys = Array.from({ length: 32 }, (_, index) => `kept-${index}`);
  const ir = analyzeJavaScriptSemantics(`let fs;
    ${keys.map((key) => `fs=require('fs'); fs.readFileSync('${key}'); fs={};`).join("\n")}
    fs=require('fs'); fs.readFileSync=custom; fs.readFileSync('wrong');`);
  expect(ir.configurationOperations.map(({ key }) => key)).toEqual(keys);
});

it.each([
  "import fs = require('fs'); fs={}; fs={}; fs.readFileSync('wrong');",
  "import fs = require('fs'); fs={},fs={}; fs.readFileSync('wrong');",
])("drops entry origins after definite replacement: %s", (source) => {
  expect(analyzeJavaScriptSemantics(source).configurationOperations).toEqual(
    [],
  );
});

it.each([
  "const fs=require('fs'); Reflect.set(fs,'readFileSync',custom,{}); fs.readFileSync('kept');",
  "const fs=require('fs'); const receiver={}; Reflect.set(fs,'readFileSync',custom,receiver); fs.readFileSync('kept');",
  "let fs=require('fs'); { fs.readFileSync('kept'); } fs={};",
  "let fs=require('fs'); { { fs.readFileSync('kept'); } } fs={};",
  "let fs=require('fs'); if(flag) { fs.readFileSync('kept'); } fs={};",
  "let fs; fs=require('fs'),fs.readFileSync('kept'); fs={};",
])(
  "retains ordered reads across receiver and statement boundaries: %s",
  (source) => {
    expect(
      analyzeJavaScriptSemantics(source).configurationOperations.map(
        ({ key }) => key,
      ),
    ).toEqual(["kept"]);
  },
);

it.each(["key", "'__proto__'"])(
  "retains uncertainty when a required argv object escapes through %s",
  (key) => {
    const ir = analyzeJavaScriptSemantics(`const proc=require('node:process');
      function run() { patch(proc.argv[${key}]); return proc.argv[3]; }`);
    expect(ir.configurationOperations.map(({ key }) => key)).not.toContain("3");
  },
);

it("retains a nested builtin read before receiver reassignment", () => {
  const ir = analyzeJavaScriptSemantics(`let fs=require('fs');
    fs.promises.open('kept'); fs={};`);
  expect(ir.resourceOperations.map(({ method }) => method)).toEqual(["open"]);
});

it("checks the parent promises slot for fresh require chains", () => {
  const ir =
    analyzeJavaScriptSemantics(`const fs=require('fs'); delete fs.promises;
    require('fs').promises.open('wrong');`);
  expect(ir.resourceOperations).toEqual([]);
});

it.each([
  "const target={__proto__:{set hook(v){this.fs.readFileSync=custom;}}}; Reflect.set(target,'hook',1,{fs});",
  "const target={fs,__proto__:{set hook(v){this.fs.readFileSync=custom;}}}; Reflect.set(target,'hook',1);",
  "const proto={set hook(v){this.fs.readFileSync=custom;}}; const target=Object.create(proto); Reflect.set(target,'hook',1,{fs});",
  "const target=getTarget(); Reflect.set(target,'hook',1,{fs});",
  "const target=require('./custom'); Reflect.set(target,'hook',1,{fs});",
  "const target={hook:0}; const alias=target; Object.defineProperty(alias,'hook',{set(v){this.fs.readFileSync=custom;}}); Reflect.set(target,'hook',1,{fs});",
  "const target={hook:0,set [key](v){this.fs.readFileSync=custom;}}; Reflect.set(target,'hook',1,{fs});",
  "const target={__proto__:{set __proto__(v){this.fs.readFileSync=custom;}}}; Reflect.set(target,'__proto__',1,{fs});",
])("preserves inherited or unknown Reflect setter effects: %s", (setup) => {
  expect(
    analyzeJavaScriptSemantics(
      `const fs=require('fs'); ${setup} fs.readFileSync('wrong');`,
    ).configurationOperations,
  ).toEqual([]);
});

it.each([
  "const target={hook:0,__proto__:{set hook(v){this.fs.readFileSync=custom;}}}; Reflect.set(target,'hook',1,{fs});",
  "Reflect.set({hook:0},'hook',1,{fs});",
  "const owner=module; Reflect.set(owner,'require',custom,fs);",
  "const target={hook:0,...props}; Reflect.set(target,'hook',1,{fs});",
])(
  "keeps a proven own data property separate from inherited setters: %s",
  (setup) => {
    expect(
      analyzeJavaScriptSemantics(
        `const fs=require('fs'); ${setup} fs.readFileSync('kept');`,
      ).configurationOperations.map(({ key }) => key),
    ).toEqual(["kept"]);
  },
);

it.each([
  "const {promises:fsp}=require('fs'); delete require('fs').promises;",
  "const fs=require('fs'); const {promises:fsp}=fs; delete fs.promises;",
  "const fs=require('fs'); let {promises:fsp}=fs; delete fs.promises;",
  "const {promises:fsp}=require('node:fs'); require('fs').promises={};",
])(
  "retains destructured objects after replacing their parent slot: %s",
  (setup) => {
    const ir = analyzeJavaScriptSemantics(
      `${setup} const h=fsp.open('kept'); h.close();`,
    );
    expect(ir.resourceOperations.map(({ method }) => method)).toEqual([
      "open",
      "close",
    ]);
  },
);

it.each([
  "delete require('fs').promises; const {promises:fsp}=require('fs');",
  "const {promises:fsp}=require('fs'); fsp.open=custom;",
  "const {promises:fsp}=require('fs'); require('fs/promises').open=custom;",
])(
  "keeps capture-before-write distinct from changed child methods: %s",
  (setup) => {
    expect(
      analyzeJavaScriptSemantics(`${setup} fsp.open('wrong');`)
        .resourceOperations,
    ).toEqual([]);
  },
);

it.each([
  "const tls=require('tls'); const net=require('net');",
  "const tls=require('node:tls'); const net=require('node:net');",
  "import * as tls from 'node:tls'; import * as net from 'node:net';",
])("distinguishes TLS and net acquisition methods: %s", (imports) => {
  const ir = analyzeJavaScriptSemantics(`${imports}
    tls.connect(443); tls.createConnection(443);
    net.connect(80); net.createConnection(80);`);
  expect(ir.resourceOperations.map(({ method }) => method)).toEqual([
    "connect",
    "connect",
    "createConnection",
  ]);
});

it.each(["spawnSync", "execSync", "execFileSync"])(
  "retains asynchronous child effects alongside native %s",
  (method) => {
    const ir = analyzeJavaScriptSemantics(`const cp=require('child_process');
      function asyncRun() { return cp.spawn('tool'); }
      function syncRun() { return cp.${method}('tool'); }`);
    expect(ir.childProcessSpawns.map(({ method }) => method)).toEqual([
      "spawn",
    ]);
  },
);

it.each([
  "module.require=other;",
  "delete module.require;",
  "Object.defineProperty(module,'require',{set(value){}});",
  "module={};",
])("keeps wrapper descriptor timing before later writes: %s", (later) => {
  const ir = analyzeJavaScriptSemantics(`const fs=require('fs');
    Reflect.set(module,'require',replacement,{fs});
    fs.readFileSync('kept'); ${later}`);
  expect(ir.configurationOperations.map(({ key }) => key)).toEqual(["kept"]);
});

it.each([
  "const fs=require('fs'); Object.defineProperty(module,'require',{set(value){this.fs.readFileSync=custom;}}); Reflect.set(module,'require',replacement,{fs}); fs.readFileSync('wrong');",
  "const fs=require('fs'); function run(){Reflect.set(module,'require',replacement,{fs}); fs.readFileSync('wrong');} Object.defineProperty(module,'require',{set(value){this.fs.readFileSync=custom;}}); run();",
])("keeps uncertain wrapper descriptor timing conservative: %s", (source) => {
  expect(analyzeJavaScriptSemantics(source).configurationOperations).toEqual(
    [],
  );
});

it.each([
  "Reflect.set=Reflect.set.bind(null,module); Reflect.set('require',replacement);",
  "Object.assign=Object.assign.bind(null,module); Object.assign({require:replacement});",
  "const set=Reflect.set; Reflect.set=set.bind(null,module); Reflect.set('require',replacement);",
  "Reflect.set=Reflect.set.bind(null,module); Reflect.set.call(null,'require',replacement);",
  "Reflect.set=Reflect.set.bind(null,module); Reflect.set.apply(null,['require',replacement]);",
  "const reflect=Reflect; reflect.set=Reflect.set.bind(null,module); Reflect.set('require',replacement);",
  "Reflect.set=Reflect.set.bind(null,module); const set=Reflect.set; set('require',replacement);",
  "globalThis.Reflect.set=Reflect.set.bind(null,module); Reflect.set('require',replacement);",
  "const set=Reflect.set; globalThis.Reflect={set:set.bind(null,module)}; Reflect.set('require',replacement);",
  "Reflect[key]=Reflect.set.bind(null,module); Reflect.set('require',replacement);",
  "Reflect.set=Reflect.set.bind(null,module); Reflect.apply(Reflect.set,null,['require',replacement]);",
  "Reflect.set=flag ? Reflect.set.bind(null,module) : other; Reflect.set('require',replacement);",
  "Reflect.set=flag && Reflect.set.bind(null,module); Reflect.set('require',replacement);",
  "Reflect.set=(0,Reflect.set.bind(null,module)); Reflect.set('require',replacement);",
  "Reflect.set=holder=Reflect.set.bind(null,module); Reflect.set('require',replacement);",
])(
  "follows assigned intrinsic values carrying the wrapper module: %s",
  (setup) => {
    expect(
      analyzeJavaScriptSemantics(
        `${setup} require('fs').readFileSync('wrong');`,
      ).configurationOperations,
    ).toEqual([]);
  },
);

it.each([
  "Reflect.set=Reflect.set.bind(null,{}); Reflect.set('require',replacement); require('fs').readFileSync('kept');",
  "Reflect.other=Reflect.set.bind(null,module); Reflect.set({},'require',replacement); require('fs').readFileSync('kept');",
  "const set=Reflect.set; Reflect.set=Reflect.set.bind(null,module); set({},'require',replacement); require('fs').readFileSync('kept');",
  "Reflect.set({},'require',replacement); require('fs').readFileSync('kept'); Reflect.set=Reflect.set.bind(null,module);",
  "Reflect.set=(Reflect.set.bind(null,module),custom); Reflect.set({},'require',replacement); require('fs').readFileSync('kept');",
  "Reflect.set=Reflect.set.bind(null,{}); function run(){Reflect.set('require',replacement); require('fs').readFileSync('kept');} run();",
])(
  "keeps unrelated or later assigned intrinsic values separate: %s",
  (source) => {
    expect(
      analyzeJavaScriptSemantics(source).configurationOperations.map(
        ({ key }) => key,
      ),
    ).toEqual(["kept"]);
  },
);
