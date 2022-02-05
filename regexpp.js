#!/usr/bin/env node
//Streaming Regex-based Macro Preprocessor (aka Fun With Regex Macros)
//- allows regex-based macros to be applied to a source file; allows DSL to be created using regex macros
//Copyright (c) 2018-2019 djulien

//rev history:
// 0.8  4/5/19  DJ  rework vm / #directive eval
// 0.81  8/10/19  DJ  fixes to work with MPASM (non-C src), use #if 0/#endif for language-neutral comments
// 0.82  8/16/19  DJ  expand macros first before checking for preprocessor commands: allows caller-defined out-commenting to bypass #directives, don't expand #defines within strings, fix #define expr arg substitution, show eval/macro results in output
// 0.84  9/7/19 DJ  TODO: reduce to 1 built-in #directive: #definex; define other directives using #definex (to create a DSL ukernel)

//to debug:
//  node inspect scripts/rexpp.js <args>
//  c, n, s, bt, .exit, repl


//alternate approach: https://stackoverflow.com/questions/3545875/custom-gcc-preprocessor
//custom control sttrs: https://www.chiark.greenend.org.uk/~sgtatham/mp/
//other choices:
//https://codegolf.stackexchange.com/questions/20721/create-a-c-preprocessor
//https://github.com/parksprojets/C-Preprocessor

//regex notes:
//https://developer.mozilla.org/en-US/docs/Web/JavaScript/Guide/Regular_Expressions
//https://stackoverflow.com/questions/7376238/javascript-regex-look-behind-alternative
//(?:x)  non-capturing match
//x(?=y)  positive lookahead
//x(?!y)  negative lookahead
//(?<=y)x  positive lookbehind
//(?<!y)x  negative lookbehind
//can't use variable len look-behinds :(   work-arounds:
//https://stackoverflow.com/questions/9030305/regular-expression-lookbehind-doesnt-work-with-quantifiers-or
//https://stackoverflow.com/questions/17286667/regular-expression-using-negative-lookbehind-not-working-in-notepad/48727748#48727748
//https://javascript.info/regexp-backreferences
//string matching:
//https://stackoverflow.com/questions/6462578/regex-to-match-all-instances-not-inside-quotes/23667311#23667311

//capture up until a string:
//https://stackoverflow.com/questions/8584697/javascript-regular-expression-match-anything-up-until-something-if-there-it-ex

//nested regex:
//https://stackoverflow.com/questions/14952113/how-can-i-match-nested-brackets-using-regex/25489964
////const str = "1ab1cd1ef2221ab1cd1ef222";
////const re = /(1(?:\1??[^1]*?2))+/;
//const str = "(ab(cd(ef)))(ab(cd(ef)))";
//const re = /(\((?:\(??[^(]*?\)))+/;
//console.error(JSON.stringify(str.match(re)));
//XRegExp plug-in: http://xregexp.com/api/#matchRecursive

//no worky:
//const str = "(ab(cd(ef)))(ab(cd(ef)))";
////const re = /\(((?>[^()]+)|(?R))*\)/g; //not impl in Javascript
//const re = /(?=\()(?:(?=(?(1).*?(?=\1)).*?\((.*))(?=(?(2).*?(?=\2)).*?\)(.*)).)+?(?>.*?(?=\1))[^(]*?(?=\2$)/g; //http://www.drregex.com/2017/11/match-nested-brackets-with-regex-new.html
//console.error(JSON.stringify(str.match(re)));
//process.exit();

//works* https://stackoverflow.com/questions/6462578/regex-to-match-all-instances-not-inside-quotes/23667311#23667311

"use strict";
require("magic-globals"); //__file, __line, __stack, __func, etc
require("colors").enabled = true; //for easier to read console output; https://github.com/Marak/colors.js/issues/127
//process.on('uncaughtException', (err) => fatal(`[UNCAUGHT] ${err}`));

//const fs = require("fs");
//const vm = require("vm"); //https://nodejs.org/api/vm.html
//const glob = require("glob");
const pathlib = require("path"); //NOTE: called it something else to reserve "path" for other var names
//const JSON5 = require("json5"); //more reader-friendly JSON; https://github.com/json5/json5
const XRegExp = require("xregexp"); //https://github.com/slevithan/xregexp
//const safe = require('safe-regex'); //https://github.com/substack/safe-regex; https://regex101.com/
//const CaptureConsole = require("capture-console"); //https://github.com/joepie91/node-combined-stream2
const nodeCleanup = require('node-cleanup'); //https://github.com/jtlapp/node-cleanup, https://stackoverflow.com/questions/14031763/doing-a-cleanup-action-just-before-node-js-exits
//const debug = //TODO
const CircularJSON = require('circular-json');

//streams:
const EventEmitter = require('events');
//TODO? const miss = require("mississippi"); //stream utils
const thru2 = require("through2"); //https://www.npmjs.com/package/through2
//const byline = require('byline'); //, {LineStream} = byline;
//kludge: LineStream() generates extra linefeeds when piped, so use wraper function API instead:
//NO WORKY: function LineStream(opts)
//{
//    if (!(this instanceof LineStream)) return new LineStream(opts);
////                .pipe(createStream(new shebang(opts), {keepEmptyLines: true}))
//    const instrm = new PassThrough(); //inner end-point
//    const outstrm = createStream(instrm, {keepEmptyLines: true, });
//    return new Duplex(outstrm, instrm); //return end-point wrapper so caller can use pipe(); CAUTION: swap in + out
//}
//const RequireFromString = require('require-from-string');
//const DuplexStream = require("duplex-stream"); //https://github.com/samcday/node-duplex-stream
//const CombinedStream = require("combined-stream2"); //
const {Readable, /*Writable, Duplex,*/ PassThrough} = require("stream");
//const Duplex = DuplexStream; //TODO: API is different
//see also https://medium.freecodecamp.org/node-js-streams-everything-you-need-to-know-c9141306be93
//const {echo_stream} = require("./dsl.js");

extensions(); //hoist to allow in-line usage further down


////////////////////////////////////////////////////////////////////////////////
////
/// Regex preprocessor (stream):
//

//common regex sub-patterns:
//using regex as lexer :)
//captures must be unnamed to allow multiple occurrences; caller can enclose within capture group if desired
//(?:x)  non-capturing match
//x(?=y)  positive lookahead
//x(?!y)  negative lookahead
//(?<=y)x  positive lookbehind
//(?<!y)x  negative lookbehind
const ESC = `\\\\`; //escape char; CAUTION: double esc here
const VisibleSpace = "\u00b7"; //String.fromCharCode(0xa4); //easier for debug of len/spacing
const ANYCHAR = `[\\s\\S]`; //`[^]`;
const WHITE = `(?: \\s+ )`; //ignore white space; caller must append "?" if optional; NOTE: matches \n
const WHITE_END = `(?: [^\\S\\n]+ )`; //white space at end of line *excluding newline*; see https://stackoverflow.com/questions/3469080/match-whitespace-but-not-newlines
//const SEP_re = /\s*,\s*/g; //new RegExp(`${WHITE},${WHITE}`, "g");
const NOT_ESC = `(?<! ${ESC} )`; //negative look-behind for escape char
const NUMBER = `(?: 0x [A-Fa-f\\d]+ | \\d+ )`; //hex or dec
const QUO_STR = `(?: ${NOT_ESC} " (?: ${ESC} " | [^"] )* " | ${NOT_ESC} ' (?: ${ESC} ' | [^'] )* ' | ${NOT_ESC} \` (?: ${ESC} \` | [^\`] )* \` )`; //don't use named capture; might occur multiple times in pattern
//const MACRO_NAME = "\w+"; //word chars: [a-z0-9_] //TODO: allow $ or @ in name?; allow regex pattern in place of name?
//const IDENT = `(?! \\d ) [\\w\\$\\@]+`; //allow "$" and "@" in identifiers; //`[A-Za-z$_][\\w\\$]*`; //`[A-Za-z\\$_][A-Za-z0-9\\$_]*`; //"\w+"; //\w[\w\d$_]*
//allow special chars to reduce need for parameterized regex macros:
const IDENT = `(?! ${NOT_ESC} \\d ) (?: ${ESC} ${ANYCHAR} | [\\w@$] )+`; //allow "$" and "@" in identifiers; can't start with digit; //`[A-Za-z$_][\\w\\$]*`; //`[A-Za-z\\$_][A-Za-z0-9\\$_]*`; //"\w+"; //\w[\w\d$_]*
const FILENAME = `(?: ${QUO_STR} | (?: ${ESC} ${ANYCHAR} | [^?:<>|&] )+ )`;
//    const QUO_STR = `\\\\ ${ANYCHAR} | " (?: \\\\ " | [^"] )* " | ' (?: \\\\ ' | [^'] )* '`; //\\\\ ['"] //match escaped quotes or quoted strings; based on https://stackoverflow.com/questions/6462578/regex-to-match-all-instances-not-inside-quotes/23667311#23667311a
//const QUO_STR = `(?<quotype> ${NOT_ESC} ['"] ) (?: ${ANYCHAR} (?! ${NOT_ESC} \\k<quotype> ) )* .?`;
//named capture only allows one str :(
//not good for >1 match: const QUO_STR = `(?<quotype> ${NOT_ESC} ['"] ) (?: ${ESC} ${ANYCHAR} | (?! \\k<quotype> ) ${ANYCHAR} )*? \\k<quotype>`; //match non-escaped quote followed by anything escaped or non-quote char up until closing quote (lazy); NOTE: can't use negative look-behind with varible len pattern; use look-ahead instead
//const QUO_STR = `( ${NOT_ESC} " (?: ${ESC} " | [^"] )* " | ${NOT_ESC} ' (?: ${ESC} ' | [^'] )* ' )`; //don't use named capture; this
const NOT_QUOTED = `${QUO_STR} |`; //`(?<! ${QUO_STR})`;
//const NOT_BRACED = `${NOT_ESC} \\{ (?: ${NOT_QUOTED} ${ESC} ${ANYCHAR} | [^}] )* \\} |`; //`(<! ...)`;
//function TEMPLATED(str) { return `${NOT_ESC} \` (?: ${ESC} \` | \\$ \\{ (?: ${NOT_QUOTED} ( \\b${name}\\b ) | ${ESC} \\} | [^}] )* \\} | [^\`] )* \` |`; } //enclosed within "`...${}...`"; CAUTION: only handles first one?
const PARAM_LIST = `(?: (?<hasargs> \\( ) ${WHITE}? (?<params> ${IDENT} (?: ${WHITE}? , ${WHITE}? (?: ${IDENT} | ${escre("...")} ) )* )? ${WHITE}? \\) )?`; //optional param list; C preproc expects no space between macro name and param list, so follow that convention here as well
//const NESTED_EXPR = ` #regex for macro param; accepts nested expr syntax with helper function
//#        (  #needs to be captured by group# so it can be replaced by position in param list; can't use named capture (names might occur multiple times)
//#            (?:
//        ${NOT_QUOTED} ${ESC} ${ANYCHAR} |  #any quoted or escaped char?
//#                (?<pushexpr> [({[] ) | | (?<popexpr> [)}\\]] ) #\( ... \) | \{ ... \} | \[ ... \]  #nested expr
//#?                ${NOT_ESC} \\( (?: ${ESC} [()] | [^()] )* \\) |
//#                \\( (?: [^({[] TBD )* \\) |
//#                \\{ (?: [^({[] TBD )* \\} |
//#                \\[ (?: [^({[] TBD )* \\] |
//#                ( [()] ) |  #nested expr begin/end (must be captured); helper function used for nesting/matchup
//        ${TAGCHAR("(", 1)} (?: ${NOT_QUOTED} [^${TAGCHAR(")", 1)}] )*? ${TAGCHAR(")", 1)}
//#                [^,]  #any param non-delimiter
//#?                [^,(){}[\\]]+  #any char that does not cause expr nesting or param delimiter (comma)
//#            )*?
//        )`; //.*?
const NESTED_EXPR = `#regex for macro param; accepts nested expr syntax with helper function
(?:
    ${NOT_QUOTED} ${ESC} ${ANYCHAR} |  #any quoted or escaped char?
    ${/*escu*/(TAGCHAR("(", 1)/*, 2*/)} (?: ${NOT_QUOTED} [^${/*escu*/(TAGCHAR(")", 1)/*, 2*/)}] )* ${/*escu*/(TAGCHAR(")", 1)/*, 2*/)} |  #expr nested within "()"
    ${ANYCHAR}*?  #any other chars (non-greedy)
)`;//.xre_tidy; //tidy() to avoid "#" and \n interaction in parent pattern
//const BODY = `( (?: \\s+ ) (?! ${escre(opts.EOL)} ) (?<body> (?: [^] (?! ${escre(opts.EOL)} ) ) [^]*? ) )?`; //skip white space; body can't start with eol delimiter
//    const BODY = `(?<body> ( ${QUO_STR} | (?! \\s* ${NOT_ESC} ${escre(opts.EOL)} ) ${ANYCHAR} )*? )`; //skip white space; body can't start with eol delimiter
//    const STMT = `(?: ${QUO_STR} | ${ESC} ${ANYCHAR} | [^;] )*?`;
//    const BLOCK = `(?: ${NOT_ESC} \\{ \\s* ${STMT} (?: \\s* ; \\s* ${STMT} )*? \\s* ${NOT_ESC} \\} )`;
//    const BODY = `(?<body> (?: ${QUO_STR} | ${NOT_ESC} \\{ (?: ${ESC} [{}] | [^{}] | ( [{}] ) )    (?! \\s* ${escre(opts.EOL)} ) ${ANYCHAR} )*? )`; //skip white space; body can't start with eol delimiter
//const BODY = `(?: ${WHITE} ${NOT_ESC} \\{ ( ${NOT_QUOTED} ${ESC} ${ANYCHAR} | [^}] )* \\} | ${WHITE} ( ${NOT_QUOTED} ${ANYCHAR} )*? )`; //skip white space; body can't start with eol delimiter
//const BODY = `(?: (?<isfunc> ${NOT_ESC} \\{ ) (?: ${NOT_QUOTED} ${ESC} ${ANYCHAR} | [^}] )* \\} | ${NOT_QUOTED} ${ESC} ${ANYCHAR} | ${ANYCHAR} )*?`; //caller should skip white space; body can't start with eol delimiter; non-greedy unbraced body allows caller to match eol
const EOL_ph = "%EOL%"; //placeholder for live EOL option value
const EOL_JUNK = `${WHITE}? (?<eol_junk> ${NOT_ESC} ${escre(EOL_ph)} ${ANYCHAR}* )? $`; //optional trailing comment
const EOL_KEEP = (keep) => `${WHITE}? (?<${keep || "keep"}> (?: ${NOT_QUOTED} ${ANYCHAR} )*? ) ${EOL_JUNK}`; //expr/body + optional trailing comment
//const EOL_BODY = EOL_KEEP.replace(/?<keep>/g, "?<body>");
//TODO: function EOL_xre(eol) { return new XRegExp(`${WHITE} (?<keep> (?: ${NOT_QUOTED} ${NOT_BRACED} ${ANYCHAR} )*? ) ${EOL_JUNK(eol)}`.anchorRE, "x"); } //optional trailing comment
const NEWLINE_SAVEJOIN = TAGCHAR("\n", 1); //kludge: preserve newlines during line joins when splitting regular newlines
//const ENDCOLOR = unesc(xre_tidy(ANSI_COLOR(false), 0)); //.replace(/\s/g, "");
const ENDCOLOR = "%".blue_lt.replace(/^.*%/, ""); //extract color-end control seq


//common regex ("g" flag for all matches):
const ANYCHAR_re = /[^]/g;
const NEWLINE_re = /\r?\n/g; //used for spliting lines
const UNICODE_re = /[\u0100-\uffff]/g; //gu; // /(?:[(){}])#\d+/g;
const COLOR_DETECT_xre = `(?<end> ${ANSI_COLOR(false)} ) | (?<start> ${ANSI_COLOR(true)} )`.XRE("gx"); //CAUTION: need to check end before start
const SRCLINE_xre = `@ (?<file> .*? ) : (?<line> ${NUMBER} (?: \\. (?<column> ${NUMBER} ) )? )`.anchorRE.XRE("gx"); //split(":"); //NOTE: need "g" for multi-srcline
//XRE.debug = true;
const LINEJOIN_xre = `${WHITE_END}? ${escre("\\")} ${WHITE_END}? \\r?\\n ${WHITE_END}?`.XRE("gx"); //CAUTION: non-std behavior: trim white space before, allow white space after "\"
const LINESPLIT_re = /[^\S\n]*\r?\n[^\S\n]*/g; //no worky: `${WHITE_END}? (?! ${escre("\\")} ${WHITE_END}? ) \\r?\\n ${WHITE_END}?`.XRE("gx"); //only split if no line continuation char found
//console.error(LINESPLIT_xre.xregexp.source.escnp.escnl, srcline());


//const regexproc =
//module.exports.regexproc =
function regexproc(opts) // = {}) //{filename, replacements, prefix, suffix, echo, debug, run, ast, shebang}; CAUTION: opts also used as vm context
{
//debug.once("" + __func);
debug.once(`expand.debug = ${expand.debug = -1} (sticky)`.red_lt);
    opts = opts || {};
    if (this instanceof regexproc) fatal(`don't use "new" with regexproc()`);
debug.once("node.js versions:".cyan_lt, process.versions); //${JSON.stringify(process.versions, null, 2)}`.cyan_lt);
debug("regexproc opts:", opts);
    expand.context.where = `@${opts.infilename || "stdin"}:1`; //run-time srcline
    return Object.assign(thru2(xform, flush), {lineproc}); //, where: `@${opts.infilename || "stdin"}:1`}); //Object.assign(thru2(/*{objectMode: false},*/ xform, flush), {pushline});
//    return Object.assign(thru2(xform, flush), {pushline}); //Object.assign(thru2(/*{objectMode: false},*/ xform, flush), {pushline});

    function xform(chunk, enc, cb)
    {
//        if (typeof chunk != "string)") chunk = chunk.toString();
        ++this.numchunks || (this.numchunks = 1);
//        const PRESERVE = TAGCHAR("\n", 1); //kludge: preserve line join indicators when splitting regular newlines
//        const NEWLINE_SAVEJOIN_xre = escre(NEWLINE_SAVEJOIN).XRE(); //need regex to get match ofs
//        const EOL_ph_xre = escre(EOL_ph).XRE();
        const frags = tostr(chunk)
            .replaceAll(NEWLINE_SAVEJOIN, (...args) => fatal(`conflict: input stream already contains tagged newline at ${/*this*/expand.context.where}.${args.at(-2)}: ${highlight(chunk, args.at(-2)/*, -100, +100*/)}`))
            .replace(LINEJOIN_xre, NEWLINE_SAVEJOIN)
            .replaceAll(EOL_ph, (...args) => fatal(`conflict: input stream already contains tagged EOL at ${/*this*/expand.context.where}.${args.at(-2)}: ${highlight(chunk, args.at(-2)/*, -100, +100*/)}`))
            .replaceAll(opts.EOL, EOL_ph) //NOTE: so generic EOL internally so system regexs/macros don't need to change
            .split(LINESPLIT_re);
debug(`chunk[${this.numchunks}] len ${chunk.length} with ${commas(plural(numlines(chunk)))} line${plural.suffix} -> ${commas(plural(frags.length))} frag${plural.suffix}`.cyan_lt, trunc(chunk, 120)); //.escnp.escnl);
//frags.forEach((frag, inx, all) => debug(`chunk[${this.numchunks}], ${typeof frag} frag[${inx}/${all.length}]:`, frag.escnp.escnl));
        frags.forEach((line, inx, all) => this.remainder = this.lineproc((this.remainder || "") + line.replaceAll(NEWLINE_SAVEJOIN, "\n"), inx == all.length - 1), this); //process input stream line-by-line for #directives to work correctly; CAUTION: need to preserve \n for correct line#s and in-line comments; NOTE: frag contains \n if lines were joined; \n matches white space so regex should still work correctly
        cb();
    }

    function flush(cb)
    {
        this.lineproc(this.remainder);
        const parts = /*this*/expand.context.where.match(SRCLINE_xre); // /^(.*):(\d+)(?:\.(\d+))$/); //split(":");
        if (!parts) fatal(`can't get srcline parts from '${/*this*/expand.context.where}'`);
        debug(`${commas(plural(Math.floor(+parts.line)))} line${plural.suffix} processed from '${parts.file}'`);
        cb(); //debug(`eof ${this.numlines} lines`); cb(); }
    }

    function lineproc(linebuf, keep_frag)
    {
//        debug(`got line ${this.numlines} ${linebuf}`);
        if (keep_frag /*|| isundef(linebuf)*/) return linebuf; //save line fragment to join with next chunk
//debug(`in[${this.numlines || 0}]:`, `${linebuf.length}:'${linebuf}'`);
//        ++this.numlines || (this.numlines = 1);
//        const parts = this.where.match(SRCLINE_xre);
//        if (!parts) fatal(`bad where: '${this.where}'`);
debugger;
//debug(`in[${this.srcline}]: ${numlines(linebuf)} lines`.red_lt);
//        if (linebuf.slice(-1) == "\\") return linebuf.slice(0, -1) + "\n"; //line continuation (mainly for macros); \n allows single-line comments
//        const LINEJOIN_xre = `${WHITE}? ${escre("\\")} ${WHITE}? $`.XRE(); //CAUTION: non-std behavior: trim white space before, allow white space after "\"
//        const parts = linebuf.match(LINEJOIN_xre);
//        return linebuf.replace(LINEJOIN_xre, (match, keep) => {});
//        const parts = linebuf.split(LINEJOIN_xre);
//        if (parts.length > 1) return parts[0] + "\n"; //keep fragment for later; CAUTION: keep \n to allow in-line JS comments
//        linebuf = linebuf.replace(EOL_ph, escre(opts.EOL)); //CAUTION: lazy eval uses latest EOL value
//        this.pushline(`${this.numlines}. ${linebuf.length}:'${linebuf.escnl}'`);
expand.debug = true;
//        expand.context.inbuf = "";
        const expanded = expand(linebuf/*.replace(EOL_ph, opts.EOL)*/, expand.context.where);
        if (!isundef(expanded)) this.pushline(tostr(expanded).replaceAll(EOL_ph, opts.EOL || "//"));
//        [keep_frag, expand.context.inbuf] = [expand.context.inbuf, ""]; //allow macros to inject text
//        return keep_frag; //expand.context.inbuf;
//const SRCLINE_xre = `@ (?<file> .*? ) : (?<line> ${NUMBER} (?: \\. (?<column> ${NUMBER} ) )? )`.anchorRE.XRE("gx");
//        if (!expand.context.where.match(SRCLINE_xre)) fatal(`can't get srcline parts from '${/*this*/expand.context.where}'`);
//        expand.context.where = /*this*/expand.context.where.replace(`(?<=:) ${NUMBER} ( \\. ${NUMBER} )? $`.XRE(), (linenum) => numlines(linebuf) + linenum); // /${opts.infilename || "stdin"}:${this.numlines}`; //use relative line#s so macros can change it; drop col# at start of each new line
        const parts = expand.context.where.match(SRCLINE_xre);
        if (!parts) fatal(`can't get srcline parts from '${/*this*/expand.context.where}'`);
        expand.context.where = `@${parts.file}:${+parts.line + numlines(linebuf)}`; //use relative line#s so macros can change it; drop col# when processing next line
//        this.numlines += numlines(linebuf) - 1; //maintain correct line#; CAUTION: linebuf can contain \n if lines were joined
        const retval = expand.context.inbuf; //allow macros to inject more text into stream
        expand.context.inbuf = "";
        return retval;
    }
}
module.exports.regexproc = regexproc;
module.exports.version = "0.9.19";


//main dictionary of defined macros:
//2 types of macros: named or regex
//both types of macros can use functions with named param lists or simple text substitutions
//text substitions are expanded before functions
//CAUTION: store other macro housekeeping somewhere else to avoid conflicts with user-defined macros
const macros = {};
module.exports.macros = macros;


//define a new macro:
//2 types: regular C pp style #define and new regex #definex
//either type can have params an use static text substitutions or a Javascript function
//macros.create =
function cre_macro(parts, /*EOL,*/ where) //, body_inx, argbuf)
{
//debug("cre macro:", JSON.stringify(parts));
    const TYPE = parts.named? "named": "regex"; //macro type: named vs. regex
    const ignore_dups = false; //~tostr(parts.flags).indexOf("D");
    const body_ofs = parts.input.indexOf(parts.body);
    if (!~body_ofs) fatal("can't find body");
//debug("input:", parts.input.escnp.escnl); //console.error(parts.input.escnp.escnl);
//debug("body start:", parts.body.indexOf("{")); //console.error(parts.body.indexOf("{"));
//debug("body:", parts.body.escnp.escnl.color_fixup); //console.error(parts.body.escnp.escnl.color_fixup);
//debug("highlight:", highlight(parts.body, parts.body.indexOf("{"))); //console.error(highlight(parts.body, parts.body.indexOf("{")));
//    if (!parts.isfunc && ~parts.body.indexOf("{")) warn(`isfunc might be wrong in body at ${where.replace(/\.\d+$/, "")}.${body_ofs}+${parts.body.indexOf("{")}: '${parts.input.slice(0, body_ofs).escnp.escnl}${highlight(parts.body, parts.body.indexOf("{"))}${parts.input.slice(body_ofs + parts.body.length).escnp.escnl}'`); //parts.isfunc = true
//    const desc = parts.name? "macro": parts.regex? "regex macro": "?UNKN TYPE?";
//xre_fixup.debug = true;
//            xre_fixup(DEFINE_xre, parts);
//debug(JSON.stringify(parts.body));
//debug(JSON.stringify(parts[3]));
//    [parts.body, parts.regex] = [pre_parse.undo(parts.body), pre_parse.undo(parts.regex)]; //undo nested pre-parse; need correct syntax to compile body
//    [parts.body, parts.regex] = [TAG_CHAR(parts.body), TAGCHAR(parts.regex)]; //undo nested pre-parse; need correct syntax to compile body
//    parts.body = pre_parse.undo(parts.body); //undo nested pre-parse; need correct syntax to compile body
//    if (body_inx && (parts.body != parts[body_inx])) warn(`body ${(parts.body || "").length}:'${parts.body}' != parts[${body_inx}] ${(parts[body_inx] || "").length}:'${parts[body_inx]}'`); //XRegExp bug?
//    if (parts.body) parts.body = TAGCHAR(parts.body); //undo nested pre-parse
//    if (parts.regex) parts.regex = TAGCHAR(parts.regex); //undo nested pre-parse
//    [parts.body, parts.regex] = [pre_parse.undo(parts.body), pre_parse.undo(parts.regex)]; //undo nested pre-parse
    parts.regex = xre_tidy(TAGCHAR(parts.regex, -1)); //promote nested "(){}"
    parts.body = TAGCHAR(parts.body); //untag and let JavaScript handle it
    const FUNCBODY_xre = `${WHITE}? \\{ ${ANYCHAR}* \\} ${WHITE}?`.anchorRE.XRE();
    parts.isfunc = parts.body.match(FUNCBODY_xre); //!parts.body.indexOf("{");
//debug.once("func xre:", xre_tidy(FUNCBODY_xre));
if (cre_macro.debug) debug(`cre ${TYPE} macro[${numkeys(macros)}]:`, parts[TYPE].cyan_lt, "delim:", parts.delim || "", "flags:", parts.flags || "", "hasargs?", !!parts.hasargs, "params:", parts.params || "", "isfunc?", !!parts.isfunc, "body:", parts.body || "", "eol junk:", parts.eol_junk || "", "where:", where); //"eol:", /*this.opts.*/EOL.escnl, srcline);
//            const param_re = (parts.params || []).map((param) => new RegExp(`\\b${param}\\b`));
//            const body = parts.params? (...params) => `${parts.body}`.replace(): parts.body; //body must be a text replace
//?            if (parts.body) parts.body = parts.body.trim(); //drop trailing spaces
//            if (parts.params) parts.body = eval(`(function ${parts.params} ${parts.body})`); //treat body as a function, include params with macro body/function; see also https://stackoverflow.com/questions/2573548/given-a-string-describing-a-javascript-function-convert-it-to-a-javascript-func
//            else parts.body = eval(`(function() { return "${parts.body || ""}"; })`);
//            parts.body = !parts.params? parts.body: //|| "": //simple string replacement
//                eval(debug(`(function ${parts.params || "()"} { ${parts.body || ""} })`, "<:regex macro body function")); //treat body as a function, include params with macro body/function; see also https://stackoverflow.com/questions/2573548/given-a-string-describing-a-javascript-function-convert-it-to-a-javascript-func
//            if (parts.params) parts.params = `match, ${parts.params}`;
//            return `function ${parts[1]}${parts[2] || "()"} { ${parts[4]} }`; //convert to function def
//            return `//define ${parts.name}`.pink_lt; //annotate source file (mainly for debug)
//            return; //no output from this line
//            opts.macros[parts.name] = {name: parts.name, args: parts.params.split(/\s*,\s*/)), body: parts.body | ""};
//            opts.macros[parts.name] = {/*pattern: new Regexp("[^a-z0-9_]" + parts[1],*/ arglist: parts.params, body: parts.body, srcline: this.srcline};
//            const EXPAND_xre = new XRegExp(`
//                ${QUO_STR} |  #match and ignore to prevent matches within strings; must be first option to override other patterns
//#                (?: \\s* ${escre(opts.EOL)} .* $ ) |  #match and ignore junk/comment at end of line (not captured); must match before macro name
//                (?: ${EOL_JUNK} $ ) |  #match and ignore junk/comment at end of line (not captured); must match before macro name
//                (?<occurrence>
//                    \\b ${escre(parts.name)} \\b  #don't match partial names
//                    ${parts.params? `\\( \\s* ${NESTED_EXPR} ( \\s* , \\s* ${NESTED_EXPR} )* \\s* \\)`: ""}  #just use var args always
//                )`.replace(/<(push|pop)expr>/g, (name, prefix) => `<${prefix}${++num_expr >> 1}>`), "gx"); //kludge: XRegExp wants unique capture names
//    let sv_rex;
//            let num_expr = 0;
//#no worky for var #args :(        ${parts.params? `\\( ${WHITE} (?: ( ${NESTED_EXPR} ) (?: ${WHITE} , ${WHITE} ( ${NESTED_EXPR} ) )* )? ${WHITE} \\)`: ""}  #just use var args always; NOTE: can't use named capture due to multiple occurrences
//    const EXPAND_xre = new XRegExp(sv_rex = xre_tidy(parts.regex || `#regex to match named macro with params
//XRE.debug = true;
//const PARAM_LIST = `(?: (?<hasargs> \\( ) ${WHITE}? (?<params> ${IDENT} (?: ${WHITE}? , ${WHITE}? (?: ${IDENT} | ${escre("...")} ) )* )? ${WHITE}? \\) )?`; //optional param list; C preproc expects no space between macro name and param list, so follow that
//debug.once("nested expr:", tostr(NESTED_EXPR));
//debug.once("nested expr:", escu(xre_tidy(NESTED_EXPR)).escnp.escnl);
//console.error("nested expr:", escu(xre_tidy(NESTED_EXPR)).escnp.escnl);
//function show(pattern) { console.error("pattern:", escu(xre_tidy(pattern)).escnp.escnl, srcline(+1)); return pattern; }
//console.error("params", xre_tidy(parts.hasargs? `\\( ${WHITE}? (?: ${(parts.params || "").split(/\s*,\s*/).map((arg) => `( ${escu(xre_tidy(NESTED_EXPR))/*.escnp.escnl*/} )`).join(` (?: ${WHITE}? , ${WHITE}? ) `)} ) ${WHITE}? \\)`: ""));
//debug("matcher:", parts.hasargs? `\\( ws ${parts.params? `(?: ${parts.params.split(/\s*,\s*/).map((arg) => arg && `( nested )`).join(` (?: ws , ws ) `)} ws )`: ""} \\)`: "(no params)");
    const EXPAND_xre = (parts.regex || `#regex to match named macro with params
#?            (?: ${"QUO_STR"} ) |  #ignore anything within a quoted string
#            (?: ${"EOL_JUNK"} ) |  #ignore comments
        ${parts[TYPE].match(/^\w/)? "\\b": ""} ${/*escre*/(parts[TYPE])} ${parts[TYPE].match(/\w$/)? "\\b": ""}  #don't match partial names (if they are alphanumeric)
#NOTE: nested "()" are tagged with nesting level so only need to match top-level "()" here; avoids need for recursive expr helper function
        ${parts.hasargs? `\\( ${WHITE}? ${parts.params? `(?: ${parts.params.split(/\s*,\s*/).map((arg) => arg && `( ${escu(xre_tidy(NESTED_EXPR), false)/*.escnp.escnl*/} )`).join(` (?: ${WHITE}? , ${WHITE}? ) `)} ${WHITE}? )`: ""} \\)`: ""}  #just use var args always; NOTE: can't use named capture due to multiple occurrences
#?            | (?: ${"ANYCHAR"} )  #ignore anything else
        `).XRE(tostr(parts.flags)/*.replace("D", "", "!global")*/ || "gx"); //.replace(/<(push|pop)expr>/g, (name, prefix) => "<${prefix}expr${++num_expr >> 1}>"), "gx"); //kludge: XRegExp wants unique capture names
//#                    ${parts.params? `\\( ${WHITE} (?: ( ${NESTED_EXPR} ) (?: ${WHITE} , ${WHITE} ( ${NESTED_EXPR} ) )* )? ${WHITE} \\)`: ""}  #just use var args always; NOTE: can't use named capture due to multiple occurrences
//#fixed #args:                    ${parts.params? `\\( \\s* ${parts.params.split(/\s*,\s*/).map((param) => (param == "...")? `${NESTED_EXPR} ( \\s* , \\s* ${NESTED_EXPR} )*`: NESTED_EXPR).join(" \\s* , \\s* ")} \\s* \\)`: ""}
//                !parts.params.length? `${parts.name} \\s* \\( \\s* \\)`:
//            const body = parts.params? (...params) => `${parts.body}`.replace(): parts.body; //body must be a text replace
//            const params_re = parts.params? parts.params/*.slice(1, -1).trim()*/.split(/\s*,\s*/).map((param) => new RegExp(`${QUO_STR} | \\b ${param} \\b`)): null;
//            if (parts.params)
//debug("params:", JSON.stringify(parts.params));
//            parts.body = !parts.params? parts.body: //|| "": //simple string replacement
//                eval(`(function(match, ...args) //param substitution
//                {
//                    return "${parts.body || ""}" ${(parts.params || "").split(/\s*,\s*/).map((arg, i) => arg? `.replace(/\\b${arg}\\b/g, args[${i}] || "")`: "").join("")};
//            })`); //xlate body to function, include params with macro body/function; see also https://stackoverflow.com/questions/2573548/given-a-string-describing-a-javascript-function-convert-it-to-a-javascript-func
//params  body   macro
//-       str    str
//(...)   str    { return str.replace(param, arg); }
//-       {}     func
//(...)   {}     func
//            if (parts.params && (parts.body[0] != "{")) parts.body = `{ return ${parts.body}; }`;
    if (parts.isfunc && parts.hasargs && !(parts.params || "").match(/^match\b/)) parts.params = `match${parts.params? `, ${parts.params}`: ""}`; //placeholder for entire match if caller did not include one
//function TEMPLATED(str) { return `${NOT_ESC} \` (?: ${ESC} \` | \\$ \\{ (?: ${NOT_QUOTED} ( \\b${name}\\b ) | ${ESC} \\} | [^}] )* \\} | [^\`] )* \` |`; } //enclosed within "`...${}...`"; CAUTION: only handles first one?
    const TEMPLATED = `TBD!`.XRE("gx");
debug.once("TBD".red_lt);
    const params_re = parts.params? parts.params.split(/\s*,\s*/).map((name) => `${TEMPLATED(name)} | ${NOT_QUOTED} ( \\b${name}\\b)`.XRE("gx")): []; //new RegExp(`\\b${name}\\b`, "g")): []; //RE used for param substitutions; only used for text (non-function) macros
//debug(JSON.stringify(parts.params), JSON.stringify(params_re));
//CAUTION: if macro body uses dependent macros, those must be defined first or don't use braces (else need to defer eval until actual usage)
//no- lazy compile: don't compile macro until first use; this allows dependent macros to be defined after function macro
//    parts.body = parts.isfunc? eval_try(debug(`(function (${parts.params || ""}) ${parts.body})`, "<:macro body function")): //use body function as-is
//        parts.params? eval_try(debug(`(function (${parts.params}) { return "${parts.body || ""}"${parts.params.split(/\s*,\s*/).slice(1-1).map((arg, inx) => `.replace(/\\b${arg}\\b/g, ${arg})`).join("")}; })`, "<:parameterized macro string")): //param substitution
//        parts.body || ""; //simple string replacement
//                    const args = get_paramlist(match) || []; //use helper function to extract possibly recursive parameters
//            else parts.body = eval(`(function() { return "${parts.body || ""}"; }`);
if (cre_macro.debug) debug(`define ${TYPE} macro[${numkeys(macros)}]`.cyan_lt, xre_abbrev(parts[TYPE])/*.escnp.escnl*/, "id:", cre_macro.seqnum + 1, "matcher:", xre_tidy(EXPAND_xre), "func?:", !!parts.isfunc, `${typeof parts.body} body:`, parts.body/*.escnl*/ || "", `${plural(params_re.length)} param${plural.suffix}:`, parts.params || "", "where:", where); //`'${this.linebuf}' => define macro '${parts.name}', body '${(parts.body || "(none)").escnl}'`);
//            if (opts.macros[parts.name]) return warn(`ignoring duplicate macro '${parts.name}' definition on ${this.srcline}, previous was on ${opts.macros[parts.name].srcline}`);
    const dup = /*defined.*/macros[parts[TYPE]];
    if (dup /*&& !ignore_dups*/) ((dup.body == parts.body)? warn: error)(`${TYPE} macro '${parts[TYPE]}' redefined at ${where} (previous was at ${dup.where})`); //if value didn't change just make it a warning (this occurs in some of the Microchip files)
//    defined.ignore_dups = false; //auto-reset for next time
    if (dup !== null) cre_macro.order.splice(cre_macro.order.length - cre_macro.num_funcs + (parts.isfunc? cre_macro.num_funcs++: 0), 0, parts[TYPE]); //defined.order.length); //put function macros after text macros; otherwise preserve order of definition
    cre_macro.debug = false; //auto-reset
    ++cre_macro.seqnum; //detect when function macros need to be re-compiled
    return macros[parts[TYPE]] = {xre: EXPAND_xre, body: /*(parts.body || "").trim(), params_re*/parts.body, isfunc: parts.isfunc, params: parts.params, params_re, where, seqnum: cre_macro.seqnum, ID: cre_macro.seqnum, type: TYPE, key: parts[TYPE], undefine: function() { undef(this.key); }}; //convert to regex for macro expander
//            return opts.EOL + `'${this.linebuf}' => define regex macro '${JSON.stringify(opts.macros[parts.regex].xre).pink_lt}'`.yellow_lt;

    function undef(key)
    {
debug("undef macro:".cyan_lt, xre_abbrev(key));
        const retval = macros[key];
        macros[key] = null; //NOTE: null performs better than delete()
        ++cre_macro.seqnum; //|| (cre_macro.seqnum = 1); //detect when function macros need to be re-compiled \\
        return retval;
    }
}//;
//Object.defineProperties(cre_macro,
//{
//!enumerable:
//    seqnum: { value: 0, writable: true, }, //allows checking for stale function macros
//    order: { value: [], writable: true, }, //text macros are applied first, then function macros
//    num_funcs: { value: 0, writable: true, }, //for updating order faster
//});
Object.assign(cre_macro, {seqnum: 0, order: [], num_funcs: 0}); //stale checking and expansion order for macro functions
module.exports.cre_macro = cre_macro;


//expand macros:
//repeats until nothing changes
//string macros are expanded first (pass 1), then function macros (pass 2), in order of definition
//#directives are just function macros
//NOTE: need to call expand() on empty lines as well; macros might append/replace linebuf
//macros.expand =
function expand(linebuf, where, want_funcs = true) //, where)
{
//Object.assign(expand, {context: /*module.exports*/ {}, count: 0, perf_time: 0, substs: 0, max_iter: 0, compiles_ok: 0, recompiles_ok: 0, compiles_err: 0, recompiles_err: 0}); //init perf stats
    ++expand.count; //|| Object.assign(expand, {count: 1, perf_time: 0, substs: 0, max_iter: 0, compiles_ok: 0, recompiles_ok: 0, compiles_err: 0, recompiles_err: 0}); //init perf stats
    expand.perf_time -= process.hrtime.bigint();
//keep expanding until no more changes:
    let num_iter, did_funcs = false;
    for (num_iter = 0; /*num_iter >= 0*/; ++num_iter) //apply macros until no more matches (not changes)
    {
        if (num_iter > 20) fatal("inf loop?");
        const svbuf = linebuf;
//if (expand.debug) pre_parse.debug = true; //pre_parse.debug ||= expand.debug;
        linebuf = pre_parse(linebuf, where); //tag nested expr for easier regex matching; compensates for no recursive regex
if (expand.debug) debug(`expand[${expand.count}] iter[${num_iter}] apply ${commas(plural(cre_macro.order.length) - cre_macro.num_funcs)}${want_funcs? "+" + commas(cre_macro.num_funcs): ""} macro${plural.suffix} to linebuf:`.blue_lt, linebuf, `from ${where} ${srcline(+1)}`.blue_lt);
//debug(`prepped iter[${num_iter}]:`, linebuf);
//expand macros
        const more_expand = cre_macro.order.every(expand_macro); //(key, inx, all) => expand_macro(macros[key], `${macros[key].isfunc? "function": "text"} macro[${inx}/${all.length}] '${key}'`)); //TODO? maybe use indexOf to kick-start regex match; OTOH, regex perf is good, don't really need to
//        sv_linebuf = linebuf;
        linebuf = TAGCHAR(linebuf); //pre_parse.undo(linebuf);
        if (linebuf == svbuf) break; //stop when no further changes; just compare result rather than trying to count substitutions
        if (!more_expand) break;
//        if (linebuf.match(NOEXPAND_re)) break; //CAUTION: exclude #definex and #if; might interfere with regex/macro handling
if (expand.debug /*&& (svbuf != linebuf)*/) debug(`old linebuf[${num_iter}]:`.cyan_lt, svbuf/*.quoted*/, where) && debug(`new linebuf[${num_iter}]:`.cyan_lt, linebuf, "highlt:", highlight(linebuf/*.quoted*/, strcmp(linebuf, svbuf), 0, strcmp.difflen), where); //, "ok to expand again?:", !linebuf.match(NOEXPAND_re)); //separate lines for easier visual compare
fatal("quit");
    }
    expand.perf_time += process.hrtime.bigint();
    if (num_iter > expand.max_iter) [expand.max_iter, expand.maxwhere] = [num_iter, where];
//debugger;
    if (expand.debug != -1) expand.debug = false; //auto-reset for next time if nono-sticky
    return /*`EXP[${expand.count - 1}]:` +*/ linebuf;

    function expand_macro(key, inx, all) //macro, desc) //, inx, all) //[name, macro]
    {
        const CONTINUE = true, CANCEL = false;
        const macro = macros[key];
        if (macro === null) return CONTINUE; //deleted (#undefine'd) macro; //console.once(`'${name}' at ${where} not a macro (deleted?)`.red_lt), false;
        if (!macro.xre) fatal(`${macros[key].isfunc? "function": "text"} macro[${inx}/${all.length}] '${trunc(key, 50)}' at ${where} invalid def?`); //not a macro (vm context contains other globals)
        const old_linebuf = linebuf;
        let found = 0;
//        for (;;) { const was_linebuf = linebuf; //kludge: replace not processing all occurrences even with "g" flag, so use a loop:
//if (expand.debug) debug(`${macros[key].isfunc? "function": "text"} macro[${inx}/${all.length}]:`, trunc(key, 50), "matches?", !!linebuf.match(macro.xre));
        let want_cancel = false;
if (expand.debug && !linebuf.match(macro.xre)) debug(`macro[${inx}/${all.length}]:`, escu(xre_tidy(macro.xre)), "!match:", escu(linebuf));
        linebuf = linebuf.replace(macro.xre, (match, ...args) => //TODO: fix "g" flag
        {
            if (want_cancel) return match; //no more changes
            if (macro.isfunc && !want_funcs) return match; //don't apply function macros to macro bodies (could interfere with JS syntax - JS is outside DSL)
//debugger;
            const input = args.pop(); //drop src str
            const ofs = args.pop(); //drop match ofs
//            const matchstr = args.shift(); //drop matched str
if (expand.debug) debug(`match[${found}] with macro[${inx}] ${macro.named || xre_abbrev(macro.xre).quoted}:`.cyan_lt, `${typeof match}:`, match, "ofs:", ofs, `${plural(args.length)} repl arg${plural.suffix}:`, /*json_tidy(JSON.stringify(args.map((arg) => TAGCHAR(arg)), null, 2))*/args, "xre flags:", macro.xre.xregexp.flags, `apply ${/*typeof (macro.cached_body || macro.body || "")*/!macro.isfunc? "text": macro.cached_body? "func": "uncompiled"} macro:`, /*macro.regex || macro.*/trunc(key, 50), "stale?", `${macro.seqnum != cre_macro.seqnum} (${macro.seqnum} vs. ${cre_macro.seqnum})`, "match str:", match); //"input str:", /*trunc(input, 80)*/input); //with ${plural(macro.params? macro.params.length: -1)} param${plural.suffix}
//lazy compile: don't (re)compile macro until first time used; this allows dependent macros to be defined after function macro (and improves performance)
            ++found;
            if (found > 20) fatal("possible loop"); //paranoid
            if (/*!num_iter &&*/ macro.isfunc && (!macro.cached_body)) //|| (macro.seqnum !== defined.seqnum))) //need to recompile macro body; only do this during first pass
            {
                const refresh = macro.cached_body? "re": "";
                macros[key] = null; //don't try to apply self to self; TODO: allow recursive macros?
expand.debug = true;
                const expanded_body = /*(macro.seqnum != cre_macro.seqnum)?*/ expand(macro.body, macro.where, false); //: macro.body; //no need to re-expand unless other macros changed since then
//debug("compile macro");
                macro.cached_body = eval_try(`function macro_func_${inx}_${macro.named || xre_abbrev(macro.xre, 1)}(${macro.params || ""}) ${expanded_body}`); //, `<:macro body function ${refresh}compile#${defined.seqnum}`)); //use body function as-is (after dependant macros expanded)
debug("compiled ok?", !!macro.cached_body);
                if (macro.cached_body) macro.seqnum = cre_macro.seqnum; //CAUTION: mark compiled first to avoid infinite recursion
                macros[key] = macro; //restore self
//                macro.params? eval_try(debug(`function (${macro.params}) { return "${expand(macro.body, macro.srcline) || ""}"${parts.params.split(/\s*,\s*/).slice(1-1).map((arg, inx) => `.replace(/\\b${arg}\\b/g, ${arg})`).join("")}; }`, `<:parameterized macro string recompile#${defined.seqnum}`)): //param substitution
//                macro.body || "", //simple string replacement
//                if (/*!num_iter &&*/ macro.isfunc && (!macro.cached_body || (macro.seqnum !== defined.seqnum))) warn(`${refresh}compile '${name}' failed`);
                ++expand[`${refresh}compiles_${macro.cached_body? "ok": "err"}`];
                if (!macro.cached_body) fatal(`compile macro ${macro.named || xre_abbrev(macro.xre, 1)} failed`); //complain because macro is needed now (lazy compile)
            }
//        if (macro.isfunc && !macro.cached_body) fatal(`failed to compile macro '${name}' at ${where}`);
//NOTE: undef/string macro bodies were converted to functions at macro definition time
            const expanded = macro.cached_body? macro.cached_body.call(expand.context /*null*/, match.toString(), ...(args.map((arg) => /*expand_arg(arg, where)*/arg && TAGCHAR(arg, -1)))/*eval_try(arg, true) || arg.toString())*/): //function call to replace text; remain unchanged if retval undef (caller should return "" if wanted)
            /*expand(*/macro.params_re.reduce((result, arg_re, inx, all) => result.replace(arg_re, /*expand_arg(args[inx], where)*/(match, argname) => argname? escrepl(TAGCHAR(args[inx], -1)): match), macro.body || ""); //, where); //CAUTION: expand macros *after* param substituion
//debug("here3");
if (expand.debug)
    if (expanded != match.toString()) debug(/*"match ofs:", ofs, "str:", trunc(matchstr, 30),*/ `before expand ${typeof match}:`, match.toString()) && debug(`after expand ${typeof expanded}:`, expanded);
//    if (expanded != match.toString()) debug(`after expand ${typeof expanded}:`, expanded, highlight(expanded, strcmp(expanded, match), -expanded.length, strcmp.difflen)/*.escnp.escnl*/, "match was:", match); //trunc(match/*.toString()*/, 80));
//    else debug("no change after replacement");
//okay, caller might want:            if ((expanded == match) /*&& (typeof macro.body != "function")*/) error(`match[${found}] didn't change after expansion: '${expanded}'`);
//                ++expand.count || (expand.count = 1);
//                if (expand.count > (expand.limit || 20))
//debug("want_canel:", want_cancel, "body?", !!macro.cached_body, "more dir?", !!tostr(expanded).match(MOREDIR_xre));
            const retval = isundef(expanded, match.toString()); //preserve original line unless macro function returns one; //NO- use ret val as-is; macro func must add quotes if needed; (typeof expanded == "string")? quote(unquote(expanded)): expanded;
            const MOREDIR_xre = `^ ${WHITE}? ${ESC}? \\# ${WHITE}? \\w`.XRE();
            want_cancel = macro.cached_body && !tostr(retval).match(MOREDIR_xre); //retval = CANCEL; //stop expansion if function returned result
//debug(`${typeof retval} retval:`, tostr(retval), "want_cancel?", want_cancel, "xre:", xre_tidy(MOREDIR_xre), MOREDIR_xre.xregexp.flags, "match?", tostr(retval).match(MOREDIR_xre));
            return retval;
        });
        if (!want_cancel && ~macro.xre.xregexp.flags.indexOf("g") && linebuf.match(macro.xre)) fatal("didn't replace all matches");
//        if (linebuf == was_linebuf) break; }
//        if (pre_parse.sv_junk) warn(`pre parse sv junk: '${pre_parse.sv_junk}'` )
//        const svsv_junk = pre_parse.sv_junk; pre_parse.sv_junk = "";
//        linebuf = pre_parse.call(this, TAGCHAR(linebuf)); //need to re-tag in case nesting changed
//        pre_parse.sv_junk = svsv_junk;
//no; found could be from prev iter: if (found && (linebuf == old_linebuf)) error(`found match but didn't change: ${linebuf}`);
debug(`${plural(found)} substitution${plural.suffix} for this macro`);
        expand.substs += found;
        if (found > (expand.max_subst || {}).count || 0) expand.max_subst = {count: found, where};
        return want_cancel? CANCEL: CONTINUE;
//        if (found > 20) { if ((++expand.total || (expand.total = 1)) > 100) process.exit(); error("possible loop"); return 0; }
//if (expand.debug && found) debug(`macro expand: ${plural(found)} expansion${plural.suffix}, buf changed? ${linebuf != old_linebuf}`);
//        return (linebuf != old_linebuf)? found: 0; //CAUTION: start from first macro against after each match to ensure deterministic behavior
//        if (linebuf != old_linebuf) debug("old linebuf:", trunc(old_linebuf, 200)) && debug("new linebuf:", trunc(linebuf, 200));
    }

//no; already expanded, just promote    function expand_arg(arg, where) { return arg && expand(TAGCHAR(arg, -1), where); } //promote + expand arg
}//;
module.exports.expand = expand;
Object.assign(expand, {context: /*module.exports*/ {}, count: 0, perf_time: 0, substs: 0, max_iter: 0, compiles_ok: 0, recompiles_ok: 0, compiles_err: 0, recompiles_err: 0}); //init perf stats


/////////////////////////////////////////////////////////////////////////////////
////
/// Command-line interface (usable in shebangs):
//

function CLI(opts) //= {})
{
    if (this instanceof CLI) fatal(`don't use "new" with CLI()`);
    const files_seen = []; //source files to process (in order)
    const startup_code = []; //Object.assign([], {join: language_neutral_join});
    const downstream_args = [];
//    process.argv_unused = {};
debugger;
    sys_macros(startup_code);
    const num_sysmacr = startup_code.length;
    opts = JSON.parse(JSON.stringify(opts || {})); //deep copy; don't alter caller's data
opts.debug = true;
//    for (let i = 0; i < process.argv.length; ++i)
//        (((i == 2)? shebang_args("#!CLI " + process.argv[i]): null) || [process.argv[i]]).forEach((arg, inx, all) => //shebang might also have args (need to split and strip comments)
//console.error("here2", process.argv.length, process.argv.splice);
    process.argv.splice_fluent(2, 1, ...(shebang_args("#!CLI " + process.argv[2]) || process.argv.slice(2, 3))) //split shebang into args and strip comments
        .forEach((arg, inx, all) =>
        {
            debug(`arg[${inx}/${all.length}]:`, /*(i == 1)? pathlib.relative(CWD, arg):*/ arg/*.quoted*/.blue_lt);
            if (inx < 2) { debug.more("=>".blue_lt, "SKIP".blue_lt); return; } //skip node + script file names
//            var parts = arg.match(/^([+-])?([^=]+)(=(.*))?$/);
//            debug.more(`${parts.name}${!isundef(parts.value)? ` = ${spquote(parts.value.toString(), "'")}`: ""}`.cyan_lt); //${opts[parts.name.toLowerCase()]}`.cyan_lt;
            startup_code.push(`\/\/arg[${inx}/${all.length}]: '${arg}'`); //kludge: maintain arg count for error messages
            set_opt(arg); //, (str) => startup_code.push(str));
        });
//debug.enabled = true;
//process.exit();
//    console.log(JSON.stringify(opts, null, "  "));
//    Object.keys(opts).forEach((key) =>
//    {
//        if (key.toLowerCase() in opts.changes) return;
//        debug_out.push(`default option: ${`${key} = ${opts[key]}`.cyan_lt}`); //show default options also
//    });
    debug.enabled = opts.debug; //|| true; //flush or discard now that caller's intention is known; gets turned off here if caller didn't specify
    debug(`${__file}:`.green_lt, `${commas(plural(files_seen.length))} source file${plural.suffix} to process:`.green_lt, files_seen.join(", "));
//    opts.infilename = (files_seen.top || "stdin").replace(/\.(?!.*\.)/g, "-wrapper."); //`${__file}-cli-in`; //"startup_code";
    if (!files_seen.length) startup_code.push("#include -"); //files.push("-"); //read from stdin if no other input files specified
    startup_code.splice(num_sysmacr, startup_code.length - num_sysmacr, ...language_neutral(startup_code.slice(num_sysmacr))); //keep sys macros at start
    return str2strm(startup_code.join("\n").replaceAll(EOL_ph, opts.EOL || "//"))
//        .pipe(echo_stream(opts))
        .pipe(regexproc(opts)) //: new PassThrough())
        .emit_fluent_delayed("args", downstream_args)
        .on(SBEVT, more_opts) //no worky
//        .on("data", (data) => { debug(`data: ${data}`.blue_lt)}) //CAUTION: pauses flow
        .on("finish", () => eof("finish"))
        .on("close", () => eof("close"))
        .on("done", () => eof("done"))
        .on("end", () => eof("end"))
        .on("error", err => { eof(`ERROR ${err}`.red_lt); process.exit(); });
//    debug("preproc: finish asynchronously".green_lt);
//    retstrm.emit("dsl-opts", opts);
//    return retstrm;

    function eof(why)
    {
//        CaptureConsole.stopCapture(process.stdout);
        debug(`${__file} stream: ${why || "eof"}`.green_lt);
        if (warn.count) console.error(`${commas(plural(warn.count || 0))} warning${plural.suffix}`.yellow_lt.color_fixup);
        if (error.count) console.error(`${commas(plural(error.count || 0))} error${plural.suffix}`.red_lt.color_fixup);
        warn.count = error.count = 0;
    }

    function more_opts(opts, inject) //no worky from here, but allow it to be called from elsewhere
    {
        debug("more opts:", opts); //JSON.stringify(opts));
        const sv_debug = debug.enabled;
        debug.enabled = []; //kludge: debug.more() within get_arg() requires buffering
        startup_code.length = 0; //clear previously processed #define/#include
        (opts || []).forEach((arg, inx, all) => debug(`more args[${inx}/${all.length}]:`, arg) && /*opts.*/get_arg(arg)); //parse new options
        debug.enabled = sv_debug;
        if (startup_code.length) inject(startup_code.join("\n")); //inject #includes and #defines into stream
    }

    function set_opt(str) //, cmd)
    {
//might as well abuse (er, leverage) regex as mush as possible:  :)
        const OPTION_xre = `
#            (?<lhs>
#                (?<onoff> [-+] )?  #turn option on/off (optional); allows caller to override either orientation of defaults
#                (?<name> (?<first> \\S ) (?<other> [^]*? ) )  #[^=\\s]+ )  #name of option; non-greedy to allow spaces within name (needed for Windows path names)
#            )
#            (?:
#                \\s*
#                =  #assign non-boolean value (optional)
#                \\s*
#                (?<value> .+ )
#            )?
#yes/no options:
            (?<onoff> [-+] )  #turn option on/off allows caller to override either orientation of defaults
            (?<yesno_opt> echo | dead | linenums | debug )
          |
#valued options:
            (?: [-+] )?  #optional
            (?<val_opt> (?<debug_opt> debug ) | eol )
            ${WHITE}? = ${WHITE}? (?<value> .+ )
          |
#macros:
            (?: [-+] )  #required but ignored
            (?: U ) (?<undef_name> ${IDENT} )
          |
            (?: [-+] )  #required but ignored
            (?: D ) (?<def_name> ${IDENT} )
            (?: = ) (?<def_value> .+ )
          |
#includes:
            (?: [-+] )  #required but ignored
            (?: I ) ${WHITE}? (?<incl_value> .+ )
          |
#files:
            (?! [-+] )  #disambiguate file names from options
            (?<file_name> ${FILENAME} )
            `/*.xre_tidy*/.anchorRE.XRE();
//debug(debug_out.join_flush("\n"));
        const parts = /*unquoescape(str)*/tostr(str).match(OPTION_xre) || {}; //|| {name: arg.unquoescaped};
        if (parts.def_name || parts.undef_name)
        {
            const [dir, cmd] = parts.def_name? ["#define", "D"]: ["#undef", "U"];
            startup_code.push(`${dir} ${(parts.undef_name || `${parts.def_name}  ${parts.def_value}`).unesc}`);
            return debug.more(`${cmd} ${(parts.undef_name || `${parts.def_name} = ${parts.def_value}`).unesc}`.cyan_lt, "MACRO".blue_lt);
        }
        if (parts.incl_value)
        {
            startup_code.push(`#incl_folder ${quote(parts.incl_value.unesc)}`);
            return debug.more(parts.incl_value.unesc.cyan_lt, "INCL_FOLDER".blue_lt);
        }
        if (parts.file_name)
        {
//            if (!files_seen.length) opts.srcfilename = parts.file_name.unesc; //`${parts.value}-out`; //assume first file is main
            files_seen.push(parts.file_name.unesc);
//                    startup_code./*pop_fluent().pushexe(*/top = `#include "${parts.name}"`;
            startup_code.push(`#include ${quote(parts.file_name.unesc)}`);
            return debug.more(parts.file_name.unesc.cyan_lt, "FILE".blue_lt);
        }
        downstream_args.push(str); //pass +/-/= options down stream
        if (parts.onoff) return debug.more(`${parts.yesno_opt.unesc} = ${opts[parts.yesno_opt.unesc] = (parts.onoff == "+")}`.cyan_lt, "OPTS".blue_lt);
        if (parts.value) return debug.more(`${(parts.debug_opt || "EOL").unesc} = ${opts[(parts.debug_opt || "EOL").unesc] = parts.value.unesc}`.cyan_lt, "OPTS".blue_lt);
        error(`invalid option: '${str}'`);
        return debug.more(str.cyan_lt, "OPTION?".blue_lt); //unknown/unhandled option
    }
}
module.exports.CLI = CLI;
if (!module.parent) process.nextTick(() => CLI().pipe(process.stdout)); //auto-run CLI after other init


const META_xre = `
    ^ ${WHITE}? ${ESC}?
    (?:
        \\#definex ${WHITE}
        (?<delim> \\S ) (?<regex> (?: ${ESC} ${ANYCHAR} | \\# [^\\n]+ \\n | (?! \\k<delim> ) ${ANYCHAR} )*? ) \\k<delim>
        (?<flags> [gmsix]+ )?
    |
        \\#define ${WHITE} (?<named> ${IDENT} )
    )
    ${PARAM_LIST}
    ${EOL_KEEP("body")}
    `.unindent/*.anchorRE*/.XRE(); // #$-{WHITE}? (?<body> \\{ [^}]*? \\} ) $-{WHITE}? //CAUTION: simplified regex here; won't handle every regex; only needs to handle bootstrap macro

//generate system macros:
//uKernel: #definex is the only built-in directive; use it to define all the other directives (rexpp is extensible DSL)
//other directives are defined to closely match standard C preprocessor behavior
//NOTE: nested/recursive expr handling needs helper function because Javascript doesn't support recursive regex
//CAUTION: at least first line of function macros needs to end with "\" so body will be attached
//CAUTION: need to regen whenever EOL changes
//TODO: move to external file; how to define WHITE, EOL_JUNK, etc?
//global.debug = debug;
function sys_macros(src_code) //, EOL)
{
//    debug("globals:".red_lt, typeof global, /*JSON.stringify(global)*/ Object.keys(global).join(","), "${srcline()}".red_lt);
//    debug("this:".red_lt, typeof this, /*JSON.stringify(this)*/ Object.keys(this).join(","), "${srcline()}".red_lt);
//    if (sys_macros.ran) fatal("system macros only need to be generated 1x");
//    cre_macro.ignore_dups = true;
//    const defs = [];
//    const src_start = src_code.length;
//    if (src_code.length) fatal("system macros aren't created soon enough");
    const bootstrap = []; //some macros need to pre-exist before creating other macros
//helper macros:
    src_code.push(`#define paranoid()  if (!this.is_rexpp) fatal("lost context \${srcline()}")`);
    bootstrap.push(src_code.top);
    src_code.push(`#define commented(str)  "${EOL_ph}" + \`\${match.toString().escnp/*.escnl*/} => \${str}\`.yellow_lt.color_fixup`);//CAUTION: "str" must be outside quotes or within braces to be expanded
    bootstrap.push(src_code.top);
    src_code.push(`#define copyof(thing)  JSON.parse(JSON.stringify(thing))`);
    src_code.push(`#define abspath(relpath)  relpath.replace(/^~(?=\/)|^~$/, process.env.HOME).replace(/^\.(?=\/)|^\.$/, process.cwd())`); //or require("os").homedir(); //resolve home dir; NOTE: only works for current user
//messages:
    src_code.push(`\\
        #definex /^ ${WHITE}? \\#((?:pragma\\s+)?message|warning|error) ${EOL_KEEP("raw_msg")}/x(msgtype, raw_msg, eol_junk) \\
        { \\
            paranoid(); \\
            const MsgTypes = {message: [console.error, "cyan_lt"], warning: [warn, "yellow_lt"], error: [error /*fatal*/, "red_lt"]}; \\
            const [func, color] = MsgTypes[msgtype]; \\
            const msg = isundef(eval_try(raw_msg, "${srcline()}"), raw_msg); \\
            func(\`[\${msgtype.toUpperCase()}] \${raw_msg}\${(msg != raw_msg)? \\\` ("\${msg}")\\\`: ""} \${eol_junk} @\${this/*.file_stack.top*/.srcline}\`[color].color_fixup); \\
            return commented(new regex macro[\${numkeys(macros) - 1}]); \\
//            return "${EOL_ph}" + \`\${match} => new regex macro[\${numkeys(macros) - 1}]\`.yellow_lt.color_fixup; \\
        }`.unindent);
//conditional directives:
    let priority = 0; //CAUTION: these macros must be executed before others
//    const IFDEF_xre = `
//        (?: \\b defined )
//        (?<name>
//            (?: \\( ) ${WHITE}? ${IDENT} ${WHITE}? (?: \\) )  #name is enclosed within "()"
//        |
//            ${WHITE} ${IDENT}  #no "()"
//        )`.unindent.XRE();
////    module.exports.IFDEF_xre = IFDEF_xre;
//    global.IFDEF_xre = IFDEF_xre; //allow eval() to find it
//module.exports.IFDEF_xre = IFDEF_xre;
    src_code.splice(priority++, 0, `\\
        #definex /^ ${WHITE}? \\#(el)?if ${EOL_KEEP("raw_expr")}/x(elif, raw_expr) \\
        { \\
            paranoid(); \\
            const IFDEF_xre = \` \\
                (?: \\b defined ) \\
                (?<name> \\
                    (?: \\( ) ${WHITE}? ${IDENT} ${WHITE}? (?: \\) )  #name is enclosed within "()" \\
                  | \\
                    ${WHITE} ${IDENT}  #no "()" \\
                )\`.unindent.XRE(); \\
            const expr = raw_expr.replace(IFDEF_xre, (match, name) => !!macros[name]); //check defined *before* eval/expand \\
            const active = eval_try(expr, "${srcline()}"); \\
            if (isundef(active)) error(\`can't eval '\${expr}'\`); \\
            if (elif) this.if_stack.top = (this.if_stack.top === false)? !!active: null; \\
            else this.if_stack.push((this.if_stack.top !== null)? !!active: null); \\
//            this.not_active = !active; \\
            return commented(conditional push (\${!!active})); \\
//            return "${EOL_ph}" + \`\${match} => conditional push (\${!!active})\`.yellow_lt.color_fixup; \\
        }`.unindent);
//    src_code.splice(0, 0, `\\
    src_code.splice(priority++, 0, `\\
        #definex /^ ${WHITE}? \\#else ${EOL_KEEP("ignored")}/x(ignored) \\
        { \\
            paranoid(); \\
            if (ignored) warn(\`ignoring junk: '\${ignored}'\`); \\
            this.if_stack.top = (this.if_stack.top !== null)? !this.if_stack.top: null; \\
//            this.not_active = !this.not_active; \\
            return commented(conditional flip (\${this.if_stack.top})); \\
//            return "${EOL_ph}" + \`\${match} => conditional flip (\${this.if_stack.top})\`.yellow_lt.color_fixup; \\
        }`.unindent);
//    src_code.splice(0, 0, `\\
    src_code.splice(priority++, 0, `\\
        #definex /^ ${WHITE}? \\#endif ${EOL_KEEP("ignored")}/x(ignored) \\
        { \\
            paranoid(); \\
            if (ignored) warn(\`ignoring junk: '\${ignored}'\`); \\
            this.if_stack.pop(); \\
//            this.not_active = !this.if_stack.top; \\
            return commented(conditional pop (\${this.if_stack.top || "empty/on"})); \\
//            return "${EOL_ph}" + \`\${match} => conditional pop (\${this.if_stack.top || "empty/on"})\`.yellow_lt.color_fixup; \\
        }`.unindent);
    src_code.splice(priority++, 0, `\\
        #definex /^ ${EOL_KEEP("line")} $/x(line) \\
        { \\
            paranoid(); \\
            if (this.if_stack.length && !this.if_stack.top)  \\
                return "${EOL_ph}" + match/*.nocolors*/.gray_dk; //disabled line \\
        }`.unindent);
//macro mgmt:
//    const IS_IDENT_xre = `^${IDENT}`.XRE();
//    global.IS_IDENT_xre = IS_IDENT_xre; //allow eval() to find it
    src_code.push(`\\
        #definex /^ ${WHITE}? \\#if(n)?def ${EOL_KEEP("raw_expr")}/x(ifndef, raw_expr, eol_junk) \\
        { \\
            paranoid(); \\
            const IS_IDENT_xre = \`^${IDENT}\`.XRE(); \\
            const expr = raw_expr.replace(IS_IDENT_xre, \`\${ifndef? "!": ""}defined($&)\`); //rewrite as "#if defined()" \\
//            return "${EOL_ph}" + \`\${match}\`.yellow_lt; \\
            return \`#if \${expr} \${eol_junk} \${EOL_ph}rewrote as regular #if\`; //use normal #if eval \\
        }`.unindent);
//    src_code.push(`\\
//        #definex /^ ${WHITE}? \\#define ${WHITE} (?<named> ${IDENT} ) ${PARAM_LIST} ${EOL_KEEP("body")}/x(named, params, body) \\
//        { \\
//            paranoid(); \\
//cre_macro.debug = true; \\
//            cre_macro({named, params, body, input: match}, srcline(+1)); \\
//            return commented(new named macro[\${numkeys(macros) - 1}]); \\
////            return "${EOL_ph}" + \`\${match} => new named macro[\${numkeys(macros) - 1}]\`.yellow_lt.color_fixup; \\
//        }`.unindent);
//    bootstrap.push(src_code.top);
//bootstrap:
//meta-macro to define all other directives:
//    eval_try(`{ const {cre_macro, debug} = require("${__filename}"); console.error(typeof cre_macro, JSON.stringify(cre_macro)); }`);
//    console.error(typeof global, /*JSON.stringify(global)*/ Object.keys(global).join(","), srcline().red_lt);
//            const global = (function(){ return this || (1, eval)("this"); }()); \\
//    src_code.push(`\\
//        #definex /^ ${WHITE}? ${ESC}? \\#definex ${WHITE} (?<delim> \\S )  #any non-space char as delim (typically "/") \\
//        (?<regex> (?: ${ESC} ${ANYCHAR} | \\# [^\\n]+ \\n | (?! \\k<delim> ) ${ANYCHAR} )*? )  #collect anything up to unescaped delim; include comments \\
//        \\k<delim>  #trailing delim same as leading delim \\
//        (?<flags> [gmsix]+ )?  #optional flags \\
//        ${PARAM_LIST}  #optional param list \\
//        #        $-{WHITE} (?<body> $-{BODY} ) \\
//        ${EOL_KEEP("body")}  #body/replacement string and optional trailing comment \\
//        /x(delim, regex, flags, params, body) \\
//        { \\
////            console.error(typeof global, /*JSON.stringify(global)*/ Object.keys(global).join(","), "${srcline()}".red_lt); \\
//            Object.assign(this, {is_rexpp: true, if_stack: [], file_stack: [], folders: []}); \\
////            console.error(typeof this, /*JSON.stringify(this)*/ Object.keys(this).join(","), "${srcline()}".red_lt); \\
//            cre_macro({regex, flags, params, body, input: match}, srcline(+1)); \\
//            debug("bootstrap:".red_lt, typeof bootstrap_macro, bootstrap_macro.where, "${srcline()}"); \\
//            bootstrap_macro.undefine(); //replace bootstrap with this one \\
//            return \`${EOL_ph}\${match} => new regex macro[\${numkeys(macros) - 1}]\`.yellow_lt; \\
//        }`.unindent);
    src_code.push(`\\
        #definex /^ ${WHITE}? ${ESC}?  \\
        (?:  \\
            \\#definex ${WHITE}  \\
            (?<delim> \\S )  #any non-space char as delim (typically "/")  \\
            (?<regex> (?: ${ESC} ${ANYCHAR} | \\# [^\\n]+ \\n | (?! \\k<delim> ) ${ANYCHAR} )*? )  #collect anything up to unescaped delim; include comments  \\
            \\k<delim>  #trailing delim same as leading delim  \\
            (?<flags> [gmsix]+ )?  #optional flags  \\
          |  \\
            \\#define ${WHITE} (?<named> ${IDENT} )  \\
        )  \\
        ${PARAM_LIST}  #optional param list  \\
#        $-{WHITE} (?<body> $-{BODY} )  \\
        ${EOL_KEEP("body")}  #body/replacement string and optional trailing comment  \\
        /x(delim, regex, flags, named, hasargs, params, body)  \\
        {  \\
debug("named:", named) && debug("params:", params) && debug("body:", body); \\
//            console.error(typeof global, /*JSON.stringify(global)*/ Object.keys(global).join(","), "${srcline()}".red_lt);  \\
            if (!this.is_rexpp) Object.assign(this, {is_rexpp: true, if_stack: [], /*file_stack: [],*/ folders: []});  \\
            paranoid();  \\
//            console.error(typeof this, /*JSON.stringify(this)*/ Object.keys(this).join(","), "${srcline()}".red_lt);  \\
//            if (~regex.indexOf("#definex")) bootstrap_macro.undefine(); //replace temp bootstrap macro with new one  \\
cre_macro.debug = true;  \\
            cre_macro({named, regex, flags, hasargs, params, body, input: match}, srcline(+1));  \\
//debug("bootstrap:".red_lt, typeof bootstrap_macro, bootstrap_macro.where, "${srcline()}");  \\
            return commented(new \${named? "named": "regex"} macro[\${numkeys(macros) - 1}]);  \\
//            return "${EOL_ph}" + \`\${match.escnp/*.escnl*/} => new regex macro[\${numkeys(macros) - 1}]\`.yellow_lt.color_fixup;  \\
        }`.unindent);
    bootstrap.push(src_code.top);
//    const META_xre = `^ ${WHITE}? ${ESC}? \\#definex ${WHITE} (?<delim> / ) ${WHITE}? (?<regex> ${ANYCHAR}+? ) / (?<flags> x ) ${PARAM_LIST} ${EOL_KEEP("body")}`/*.anchorRE*/.XRE(); // #$-{WHITE}? (?<body> \\{ [^}]*? \\} ) $-{WHITE}? //CAUTION:
//    const DEFINEX_xre = `
//        ${WHITE}? \\#definex ${WHITE} (?<delim> \\S )  #any non-space char as delim (typically "/")
//        (?<regex> (?: ${ESC} ${ANYCHAR} | (?! \\k<delim> ) ${ANYCHAR} )*? )  #collect anything up to unescaped delim
//        \\k<delim>  #trailing delim same as leading delim
//        (?<flags> [gmsixD]+ )?  #optional flags; custom: "D" to silently allow duplicates
//        ${PARAM_LIST}  #optional param list
//#        ${WHITE} (?<body> ${BODY} )
//        ${EOL_KEEP}  #body/replacement string and optional trailing comment
//        `.anchorRE.XRE();
//    defs.push(`\\
//        #definex / ${DEFINEX_xre} /xD()
//        `)
    src_code.push(`\\
        #definex /^ ${WHITE}? \\#undef(?:ine)? ${WHITE} ${EOL_KEEP("name")}/x(name)  #(?<name> ${IDENT} ) \\
        { \\
            paranoid(); \\
            const mactype = !macros[name]? (error(\`undefined macro '\${name}' at \${this/*.file_stack.top*/.srcline}\`), "unknown"): \\
                macros[name].undefine().type; \\
//            return "${EOL_ph}" + \`\${match} => undefine \`.yellow_lt; \\
            return commented(undefine \${mactype} macro); \\
//            return "${EOL_ph}" + \`\${match} => undefine \${mactype} macro\`.yellow_lt.color_fixup; \\
        }`.unindent);
    src_code.push(`\\
        #definex /^ ${WHITE}? \\#dump ${EOL_KEEP("ignored")}/x(ignored) \\
        { \\
            const dumpout = []; \\
            if (ignored) warn(\`ignoring junk: '\${ignored}'\`); \\
            paranoid(); \\
            dumpout.push(\`\${commas(plural(numkeys(macros)) || "no")} macro\${plural.suffix}:\`.yellow_lt); \\
            Object.entries(macros).map(([key, macro], inx, all) => dumpout.push(\`\${macro.isfunc? "func": "text"} macro[\${inx}/\${all.length}]: \${key.cyan_lt} => \${macro.xre? macro.body: "(deleted)"} from \${macro.where}\`.yellow_lt.color_fixup)); \\
//            return dumpout.map((line) => \`${EOL_ph}\${line}\\n\`).join(""); \\
//            return "${EOL_ph}" + \`\${match} => \${dumpout.join("\\n${EOL_ph}".reset)}\`.yellow_lt.color_fixup; \\
            return commented() + dumpout.join("\\n${EOL_ph}"); //CAUTION: no color to left of EOL \\
//            return "${EOL_ph}" + \`\${match} => \`.yellow_lt + dumpout.join("\\n${EOL_ph}"); //CAUTION: no color to left of EOL \\
        }`.unindent);
//source file mgmt directives:
    src_code.push(`\\
        #definex /^ ${WHITE}? \\# ${WHITE}? (?<linenum> ${NUMBER} ) ${WHITE} ${EOL_KEEP("filename")}/x(linenum, filename)  #(?<filename> ${QUO_STR} )? \\
        { \\
            paranoid(); \\
            const srcparts = this.srcline.match(SRCLINE_xre); \\
            this/*.file_stack.top*/.srcline = \`@\${filename || srcparts.filename}:\${linenum}\`; \\
            return commented(srcline \${this/*.file_stack.top*/.srcline}); \\
//            return "${EOL_ph}" + \`\${match} => srcline \${this/*.file_stack.top*/.srcline}\`.yellow_lt.color_fixup; \\
        }`.unindent);
    src_code.push(`\\
        #definex /^ ${WHITE}? \\#include ${EOL_KEEP("expr")}/x(expr) \\
        { \\
            paranoid(); \\
            const filename = isundef(eval_try(expr, "${srcline()}"), expr).unquoted; \\
//            global.iostr.pause(); \\
//            this.file_stack.push(filename); \\
//            global.iostr.resume(); \\
            const try_folders = copyof(this.folders); \\
            filename = filename.replace(/^<(.*)>$/, try_folders.push(__dirname, "/include", "/usr/include") && "&1"); //add code folder and default system/global locations *after* caller-defined folders to allow caller to override system-defined files \\
//console.once(\`#incl using \${try_folders.join(", ")}\`.red_lt); \\
//    folders.forEach((folder) => debug(folder) && debug(pathlib.resolve(folder, filename), fs.existsSync(pathlib.resolve(folder, filename)))); \\
            const filepath = try_folders.reduce((found, next) => fs.existsSync(next = pathlib.resolve(next, filename))? next: found, ""); //|| filename; \\
            if (!filepath) return error(\`file '\${filename}' not found in \${plural(try_folders.length).toString().replace(/^1$/, "current")} folder\${plural.suffix}:\${try_folders.join(", ")}\`);
//            else
//        try{
//            fs.createReadStream(filepath), //pathlib.resolve(CWD, filename)), \\
//            { \\
//                linebuf: this.opts.dead? this.opts.EOL + \`\${this.linebuf} \${this.opts.EOL}depth \${this.opts.file_depth}: '\${filepath}'\`.green_lt: "", \\
//                filename: pathlib.relative(CWD, filename), \\
//            }); \\
//            return "${EOL_ph}" + \`\${match} => file '\${filename}' depth \${this.file_stack.length}\`.yellow_lt.color_fixup; \\
            const srcparts = this.srcline.match(SRCLINE_xre); \\
            this.inbuf = \`#line 1 "\${filename}"\\n\` + fs.readFileSync(filepath) + \`\\n#line \${1 + srcparts.linenum} "\${srcparts.filename}"\`; \\
//TODO: stream + skip shebang; \\
            return commented(file '\${filename}); \\
//            return "${EOL_ph}" + \`\${match} => file '\${filename}'\`.yellow_lt.color_fixup; \\
        }`.unindent);
    src_code.push(`\\
        #definex /^ ${WHITE}? \\#incl_folder ${EOL_KEEP("expr")}/x(expr) \\
        { \\
            paranoid(); \\
            const folder = isundef(eval_try(expr, "${srcline()}"), expr); \\
            const abs_folder = abspath(folder); \\
            const fold_ok = (glob.sync(abs_folder) || [])[0]; \\
//debug(\`incl folder '\${folder}', exists? \${fold_ok || false}\`); \\
            if (!fold_ok) warn(\`folder not found: '\${folder}'\`); \\
            else this.folders.push(fold_ok || abs_folder); \\
            return commented(folder[\${this.folders.length - 1}] '\${this.folders.top}'); \\
//            return "${EOL_ph}" + \`\${match} => folder[\${this.folders.length - 1}] '\${this.folders.top}'\`.yellow_lt.color_fixup; \\
        }`.unindent);
//misc:
//not needed: (just define regular macro + execute it)
//    src_code.push(`\\
//        #definex /^ ${WHITE}? \\#exec } ${EOL_KEEP("body")} $/xD(body) \\
//        { \\
//            return eval_try(\`(${body || ""})\`); \\
//        }`.unindent);
//    src_code.push("#dump"); //check sys macros were defined correctly
//manually build bootstrap macros:
//trying to reuse #definex regex
//CAUTION: EOL placeholders are left as-is; no need to substitute correct value since everything uses EOL_ph during bootstrap
//XRE.debug = true;
//const frags = tostr(chunk).replace(LINEJOIN_xre, PRESERVE).split(LINESPLIT_re);
//debug("raw bootstrap macro:", src_code.top.escnp.escnl);
    const prepped = bootstrap.map((src, inx, all) => src.replace(LINEJOIN_xre, NEWLINE_SAVEJOIN).split(LINESPLIT_re).map((frag) => frag.replaceAll(NEWLINE_SAVEJOIN, "\n"))); //"\n"); //.replace(EOL_ph, escre(EOL)); //CAUTION: need to preserve \n until comments stripped; really no need to strip comments
//bootstrap.forEach((mac, inx, all) => debug(`bootstrap macro[${inx}/${all.length}]:`, mac.escnp.escnl));
//    const SKIP_DEFINEX_xre = `^ ( ${LINEJOIN_xre.raw_src || LINEJOIN_xre.source} )* ${ESC}? \\#definex ${WHITE}`.XRE(); //skip directive in lieu of input stream handling
//    const bootstrap = xre_tidy(defs/*.shift()*/[0].replace(SKIP_DEFINEX_xre, "").replace(EOL_ph, escre(EOL, EOL))).replace(LINEJOIN_xre, " "); //, "<: defx src").match(META_xre); //CAUTION: can't strip newlines until regex comments are removed; esc EOL to avoid conflict with special chars
//    const meta = pre_parse(defs.shift().replace(EOL_ph, escre(eol)).replace(LINEJOIN_xre, "")); //, "<: defx src").match(META_xre); //NOTE: don't need line joiners
//XRE.debug = true;
//    const META_xre = `^ ${WHITE}? ${ESC}? \\#definex ${WHITE} (?<delim> / ) ${WHITE}? (?<regex> ${ANYCHAR}+? ) / (?<flags> x ) ${PARAM_LIST} ${EOL_KEEP("body")}`/*.anchorRE*/.XRE(); // #$-{WHITE}? (?<body> \\{ [^}]*? \\} ) $-{WHITE}? //CAUTION: simplified regex here; won't handle every regex; only needs to handle bootstrap macros
    prepped.forEach((frags, inx, all) =>
    {
        if (frags.length > 1) fatal(`bootstrap macro[${inx}/${all.length}] > 1 frag (${frags.length}): ${frags.map((str) => `${str.length}:'${trunc(str, 40).escnp/*.escnl*/}'`)}`);
        debug(`bootstrap macro[${inx}/${all.length}]:`, frags[0]);
        const parts = frags[0].match(META_xre);
        if (!parts) fatal(`can't parse bootstrap macro[${inx}/${all.length}]: '${frags[0].escnp/*.escnl*/}'`);
cre_macro.debug = true;
//no worky:    module.exports.bootstrap_macro = cre_macro(parts, "sys_macros:1");
        const macro = cre_macro(parts, "sys_macros:1");
        if (~(parts.regex || "").indexOf("definex")) global.bootstrap_macro = macro;
    });
//debug("globals:".red_lt, typeof global, /*JSON.stringify(global)*/ Object.keys(global).join(","));
//    bootstrap_macro
//    src_code.push(`\\
//        #define dsl_init() \\
//        { \\
//            debug("here1".red_lt); \\
//            const if_stack = []; \\
//            const file_stack = []; \\
//        }
//        dsl_init();
//        `.unindent);
//    return src_code.splice_fluent(0, 0, ...defs); //inject system macros at start
}


//input line pre-parse:
//tag nested "()" and "{}" for easier matching (allows regex to handle recursive/nested expr)
//comments are left in place; ??????????????comments are removed and re-added later
//to untag just call TAGCHAR()
function pre_parse(str, /*EOL,*/ where) //, incl_comments) //, cb)
{
//    const opts = {}; //not needed
    str = tostr(str);
    if (str.match(UNICODE_re)) fatal(`input stream already contains tagged (Unicode) chars: '${str.escnp/*.escnl*/}' at ${where} - char tag logic needs to be replaced`);
//no:pass opts as 2nd arg to also check comments
//    const EOL_JUNK = `${WHITE} (?<eol> ${NOT_ESC} ${escre(/*opts.*/ (incl_comments || {}).EOL)} ${ANYCHAR}* $ )?`; //optional trailing comment
//    if (!nested.undo) nested.undo = function (str) { return (str || "").replace(TAGCHAR.FIND_re, (tagged) => TAGCHAR(tagged)); } //remove tags
//const EOL_ph = "%EOL%"; //placeholder for live EOL option value
//const EOL_JUNK = `${WHITE}? (?<eol_junk> ${NOT_ESC} ${/*escre*/(EOL_ph)} ${ANYCHAR}* )? $`; //optional trailing comment
//const EOL_KEEP = (keep) => `${WHITE}? (?<${keep || "keep"}> (?: ${NOT_QUOTED} ${NOT_BRACED} ${ANYCHAR} )*? ) ${EOL_JUNK}`; //expr/body +
//    const EOL_xre = EOL_KEEP().replace(EOL_ph, /*pre_parse.eol*/EOL).XRE();
//    const line_parts = tostr(str).match(EOL_xre);
//    if (!line_parts) fatal(`can't find eol parts: ${str.length}:'${escnp(str)}' at ${srcline}`);
//    [str, pre_parse.sv_junk] = [line_parts.keep || "", line_parts.junk || ""];
//kludge: Javascript doesn't support recursive regex
//tag "()" and "{}" with nesting level so nested expr *can* be matched using regex:
//based on ideas from:
//  https://stackoverflow.com/questions/14952113/how-can-i-match-nested-brackets-using-regex/25489964
//  https://twiki.org/cgi-bin/view/Blog/BlogEntry201109x3
//NOTE: only need 1 outer level "{}" (for macro bodies) and outer 2 levels "()" (for nested macro calls)
//    const sv_str = eol_parts.keep; //str;
//XRE.debug = true;
    const parts = str.match(META_xre);
    const skip_len = parts? str.indexOf(parts.body): 0; //pre-parse body only of #definex, not regex (likely won't be properly nested)
if (pre_parse.debug) debug("pre_parse:", str, "skip len:", skip_len);
//    const NONQUOTED_EOL_JUNK = `${WHITE}? (?: ${NOT_ESC} (?: ${NOT_QUOTED} ${escre(EOL_ph)} ) ${ANYCHAR}* )? $`; //optional trailing comment
    const NESTING_xre = `
        (?: ${NOT_QUOTED} ${ESC} ${ANYCHAR} ) |  #ignore anything within a quoted string or escaped chars; CAUTION: put this before EOL check to allow quoted EOL to be used as normal string within macro body
        (?: ${EOL_JUNK.replace(/<eol_junk>/, ":")/*.replaceAll(EOL_ph, escre(EOL))*/} ) |  #exclude anything after end-of-line marker; not captured
#no, just tag it:        (?: \\( \\? [:=!<] )  #capture/look-around
#        (?<paren> (?<opparen> \\( ) | \\) ) | (?<brace> (?<opbrace> \\{ ) | \\} )  #these are the only chars needed
        (?<spchr> [(){}] )  #these are the only chars needed
#?        | (?: {$ANYCHAR} )  #ignore anything else
        `/*.xre_tidy*/.XRE("gx");
//#        ${!incl_comments? `(?: ${EOL_JUNK} ) |`: ""}  #ignore comments
//    const state = {parens: [], braces: []};
//if (pre_parse.debug) debug.once("pre_parse: nesting re:", xre_tidy(NESTING_xre));
    const state = new (function pre_parse_state()//Object.defineProperties({parens: [], braces: [], count: 0},
    {
        this.count = 0;
        this.parens = [];
        this.braces = [];
//        get self() { return this; },
//TODO: combine parens + braces into single stack?
//        parens: { value: [], }, //0, writable: true, },
//        braces: { value: [], }, //0, writable: true, },
//        "(": { get() { return TAGCHAR("(", push_fluent(this.parens, this.ofs).length - 1); }, }, //TAGCHAR("(", this.parens++); }, },
//        ")": { get() { return TAGCHAR(")", pop_fluent(this.parens).length); }, }, //--this.parens); }, },
//        "{": { get() { return TAGCHAR("{", push_fluent(this.braces, this.ofs).length - 1); }, }, //this.braces++); }, },
//        "}": { get() { return TAGCHAR("}", pop_fluent(this.braces).length); }, }, //--this.braces); }, },
//        "(": { value: function(ofs) { return TAGCHAR("(", this.parens.push_fluent(ofs).length - 1); }, }, //TAGCHAR("(", this.parens++); }, },
//        get self() { return this; },
//        this["("] = function(ofs) { debug(typeof this); debug(Array.isArray(this.parens), typeof this.parens); return TAGCHAR("(", this.parens.push_fluent(ofs).length - 1); }; //TAGCHAR("(", this.parens++); }, },
//        Object.defineProperty(this, "(", {value: (ofs) => { debug(typeof this, Array.isArray(this.parens), typeof this.parens); return TAGCHAR("(", this.parens.push_fluent(ofs).length - 1); }}); //TAGCHAR("(", this.parens++); }, },
        Object.defineProperties(this,
        {
//            "(": {value: (ofs) => { debug(typeof this, Array.isArray(this.parens), typeof this.parens); return TAGCHAR("(", this.parens.push_fluent(ofs).length - 1); }, }, //TAGCHAR("(", this.parens++); }, },
            "(": {value: (ofs) => TAGCHAR("(", this.parens.push_fluent(ofs).length - 1), }, //TAGCHAR("(", this.parens++); }, },
            ")": {value: () => TAGCHAR(")", this.parens.pop_fluent(this.count++).length), }, //--this.parens); }, },
            "{": {value: (ofs) => TAGCHAR("{", this.braces.push_fluent(ofs).length - 1), }, //this.braces++); }, },
            "}": {value: () => TAGCHAR("}", this.braces.pop_fluent(this.count++).length), }, //--this.braces); }, },
        });
//        debug(this, typeof this["("]);
//        this["("](0);
//        this[")"]();
    })();
//debugger;
//debug(JSON.stringify(state));
//debug("nest str:", str);
//const instr = args.pop(); //drop src str
//const ofs = args.pop(); //drop match ofs
//    str = str.replace(NESTING_xre, (delim, paren, opparen, brace, opbrace, ofs) => paren? (opparen? (state.ofs = ofs, state[delim]) || delim); //debug(isundef(state[delim], delim), `<:chr ofs ${delim.index || delim.startIndex}`)); //state[delim] || delim); //&& debug(delim)); //state[delim] || `\\x${delim.charCodeAt(0).toString(16)}`); //`$&#${state[delim] || 0}`); //add tags to delimiters for easier match-up within regex; CAUTION: state[] must be 0 for top-level, and can only be evaluated 1x here due to side effects
//    str = str.replace(NESTING_xre, (chr, ofs) => (state[chr] || nop)(ofs)); //debug(isundef(state[delim], delim), `<:chr ofs ${delim.index || delim.startIndex}`)); //state[delim] || delim); //&& debug(delim)); //state[delim] || `\\x${delim.charCodeAt(0).toString(16)}`); //`$&#${state[delim] || 0}`); //add tags to delimiters for easier match-up within regex; CAUTION: state[] must be 0 for top-level, and can only be evaluated 1x here due to side effects
//    if (pre_parse.debug)
//        if (tostr(str).replace(NESTING_xre, (match/*, spchr, ofs*/, ...args) => debug("found special char:", match.spchr, `at ofs ${args.at(-2)}`, JSON.stringify(args))) == str)
//            debug("pre_parse: no special char found");
    const tagged = str.slice(0, skip_len) + str.slice(skip_len).replace(NESTING_xre, (match, spchr, ofs, instr) => (state[spchr] || (()=>match))(ofs)); //debug(isundef(state[delim], delim), `<:chr ofs ${delim.index
//debug(state);
    if (state.parens.length || state.braces.length) warn(`unmatched parens or braces in '${str.split("").map((ch, inx) => ((inx in state.parens) || (inx in state.braces))? ch.blue_lt: ch).join("")}' at ${where}: ${commas(plural(state.parens.length))} paren${plural.suffix}:${state.parens.join(",")}, ${commas(plural(state.braces.length))} brace${plural.suffix}:${state.braces.join(",")}`);
    if (pre_parse.debug && (tagged != str)) debug(`${commas(plural(state.count + state.parens.length + state.braces.length))} nested tag${plural.suffix}:`, tagged.split("").map((ch, inx) => (str[inx] != ch)? ch.yellow_lt: ch).join("")); //length}:'${escu(sv_str, true)}' => ${str.length}:'${escu(str, true)}'`); //, str.replace(TAGCHAR.FIND_re, (nested) => `\\x${nested.charCodeAt(0).toString(16)}`.cyan_lt)); //TAGCHAR(nested).cyan_lt));
//    if (str != line_parts.keep) debug("pre-parse before:", line_parts.keep.length, line_parts.keep) && debug("pre-parse after: ", str.length, str);
//    const retval = cb(str); //allow caller to do something with nested tags
//    if (str != sv_str) str = str.replace(NESTTAGS_re, (tags) => ""); //strip tags off so they don't interfere
    if (tagged.length != str.length) fatal(`string length changed: ${str.length} -> ${tagged.length}`); //put this after debug()
    pre_parse.debug = false; //auto-reset for next time
//if (str.length > 1250) fatal("quit");
    return tagged; //+ EOL + pre_parse.sv_junk; //retval;
}
//pre_parse.undo = function undo_pre_parse(str) //undo pre-parse: remove char tags, re-add comment
//{
////    return /*color_preserve((str || "")*/tostr(str).replace(TAGCHAR.FIND_re, (tagged) => TAGCHAR(tagged)) + pre_parse.sv_junk); //remove tags, re-add comments
//    return TAGCHAR(str) + pre_parse.sv_junk; //untag: remove nesting tags, re-add comments
//};


////////////////////////////////////////////////////////////////////////////////
////
/// Shebang handling:
//

const SBEVT = "#!opts[]";
const NON_DELIM = `[^\\s\\#]`;
//XRE.debug = true;
const SHEBANG_xre = `
    (?<is_shebang> ^ ${WHITE}? \\# ! (?: ${QUO_STR} | ${ESC} ${ANYCHAR} | ${NON_DELIM} )+ ${WHITE_END} ) |  #shell command at start of line
    (?: [\\#\\n] ${ANYCHAR}* $ ) |  #skip trailing white space or comment (greedy, not captured)
    (?<keep> (?: ${QUO_STR} | ${ESC} ${ANYCHAR} | ${NON_DELIM} )+ )  #kludge: need explicit capture here; match[0] will include leading/trailing stuff even if not captured
    ${WHITE_END}  #eat trailing white space up until newline
    `/*.xre_tidy*/.XRE("gx");


//text stream:
//handles "#!" (shebang) if found at start of stream:
function shebang(opts)
{
    opts = opts || {};
if (this instanceof shebang) fatal(`don't use "new" with shebang()`);
//    return Object.assign(thru2(xform, flush), {pushline}); //Object.assign(thru2(/*{objectMode: false},*/ xform, flush), {pushline});
    return thru2(xform, (cb) => cb()); //flush); //Object.assign(thru2(/*{objectMon expde: false},*/ xform, flush), {pushline});

    function xform(chunk, enc, cb)
    {
//        const SHEBANG_xre = XRegExp(`
//            ^  #start of line
//#            (?<shebang>
//            \\s* \\# !  #ignore white space (non-standard?); NOTE: real shebang doesn't allow white space
//            [^\\n]*  #shebang args (greedy)
//#            )
//#            (?<remainder>
//#            \\n?
//#                .*
//#            )
//            `, "x");
//            `.anchorRE, "x");
//        if (isNaN(++this.numchunks)) this.numchunks = 1;
        ++this.numchunks || (this.numchunks = 1);
        if (typeof chunk != "string") chunk = chunk.toString(); //TODO: enc?
//debug(`shebang[${this.numlines}]: '${chunk.escnl}'`); //replace(/\n/g, "\\n")}'`);
//        if (!opts.shebang && !this.chunks.length && chunk.match(/^\s*#\s*!/)) { this.chunks.push(`//${chunk} //${chunk.length}:line 1`); cb(); return; } //skip shebang; must occur before prepend()
//            if (!opts.shebang && (this.linenum == 1) && chunk.match(/^\s*#\s*!/)) { this.chunks.push("//" + chunk + "\n"); cb(); return; } //skip shebang; must occur before prepend()
//NOTE: input stream does not need to be split by newlines here, because #! is only checked first time
//        var parts;
        if (!opts.shebang && (this.numchunks == 1))
        {
//            if (parts = chunk.match(SHEBANG_xre)) chunk = opts.EOL + parts.shebang.blue_lt; //`${chunk} //${chunk.length}:line 0 ${opts.filename || "stdin"}`.blue_lt; //cb(); return; } //skip shebang; must be first line
//debug(trunc(chunk, 100));
//            const firstline = chunk.leftof("\n");
//debug(firstline);
//            const parts = chunk.match(SHEBANG_xre);
//            if (parts)
            const more_opts = shebang_args(chunk); //firstline); //shebang might also have args (need to split and strip comments)
//debug((more_opts || []).length, JSON.stringify(more_opts));
            if ((more_opts || []).length)
            {
                if (!this.listenerCount(SBEVT)) this.on(debug(SBEVT, "<: hooked SB EVT"), opts.get_opts); //kludge: top level CLI not getting events; handle it here instead
                this.emit(SBEVT, more_opts, (str) => chunk = chunk.replace(/$/m, debug("\n" + str, "injected".cyan_lt))); //NOTE: synchronous; inject #includes and #defines into stream
            }
//            if (more_cmds.length > 1) chunk = chunk.replace(/$/m, more_cmds.join("\n")); //inject #includes and #defines into stream
            chunk = chunk.replace(SHEBANG_xre, (match) => opts.dead? opts.EOL + match.blue_lt: ""); //comment out shebang (first line only); CAUTION: chunk contains > 1 line input (due to buffering)
debug("new shebang line:", trunc(chunk/*.escnl*/, 200));
//            else debug(`no shebang: ${chunk.slice(0, 100).escnl}`.blue_lt);
//            chunk = chunk.replace(SHEBANG_xre, (match) => opts.EOL + match.blue_lt); //.echo_stderr(`shebang replace: '${chunk.slice(0, 100).escnl}'...`); //`${chunk} //${chunk.length}:line 0 ${opts.filename || "stdin"}`.blue_lt; //cb(); return; } //skip shebang; must be first line
//            if (chunk.match(SHEBANG_xre)) chunk = opts.EOL + chunk.blue_lt; //.echo_stderr(`shebang replace: '${chunk.slice(0, 100).escnl}'...`); //`${chunk} //${chunk.length}:line 0 ${opts.filename || "stdin"}`.blue_lt; //cb(); return; } //skip shebang; must be first line
        }
        /*if (opts.dead)*/ this.push/*line*/(chunk); //CAUTION: don't check opts.dead here; chunk contains > first line
        cb();
    }
//    function flush(cb) { cb(); }
}
module.exports.shebang = shebang;


//split shebang string into separate args:
//shebang args are space-separated in argv[2]
//some test strings:
// #!./prexproc.js +debug +echo +hi#lo ./pic8-dsl.js "arg space" \#not-a-comment +preproc "not #comment" -DX -UX -DX=4 -DX="a b" +echo +ast -run -reduce -codegen  #comment out this line for use with .load in Node.js REPL
// #!./prexproc.js +debug +echo +hi\#lo ./pic8-dsl.js "arg space" \#not-a-comment +preproc "not #comment" -DX -UX -DX=4 -DX="a b" +echo +ast -run -reduce -codegen  #comment out this line for use with .load in Node.js REPL
// #!./prexproc.js +debug +echo ./pic8-dsl.js xyz"arg space"ab \#not-a-comment +preproc p"not #comment" -DX -UX -DX=4 -DX="a b"q +echo +ast -run -reduce -codegen  #comment out this line for use with .load in Node.js REPL
// #!./prexproc.js +debug +echo ./pic8-dsl.js -DX -UX -DX=4 -DX="a b" +preproc +ast -run -reduce -codegen  #comment out this line for Node.js REPL .load command
function shebang_args(str)
{
    debug("shebang line?:", leftof(str, "\n")); //CAUTION: str might be multi-line chunk
//    if (!which) str = str.replace(/\s*#.*$/, ""); //strip comments
//    return (which < 0)? [str]: str.split(" "); //split into separate args
/*
    const COMMENT_xre = XRegExp(`
        \\s*  #skip white space
        (?<! [\\\\] )  #negative look-behind; don't want to match escaped "#"
        \\#  #in-line comment
        .* (?: \\n | $ )  #any string up until newline (non-capturing)
        `, "x");
    const UNQUO_SPACE_xre = /\s+/g;
//https://stackoverflow.com/questions/366202/regex-for-splitting-a-string-using-space-when-not-surrounded-by-single-or-double
    const xUNQUO_SPACE_xre = XRegExp(`
        ' ( .*? ) '  #non-greedy
     |  " ( .*? ) "  #non-greedy
     |  \\S+
        `, "xg");
    const KEEP_xre = XRegExp(`
        \\s*
        (  #quoted string
            (?<quotype> (?<! \\\\ ) ['"] )  #capture opening quote type; negative look-behind to skip escaped quotes
            (?<quostr>
                (?: . (?! (?<! \\\\ ) \\k<quotype> ))  #exclude escaped quotes; use negative lookahead because it's not a char class
                .*?  #capture anything up until trailing quote (non-greedy)
            )
            \\k<quotype>  #trailing quote same as leading quote
        |  #or bare (space-terminated) string
            (?<barestr>
#                ( (?<! [\\\\] ) [^\\s\\n\\#] )+  #any string up until non-escaped space, newline or "#"
                (?: . (?! (?<! \\\\ ) [\\s\\n\\#] )) +  #exclude escaped space, newline, or "#"; use negative lookahead because it's not a char class
                .*?  #capture anything not above (non-greedy)
                (?: [\\s\\n\\#] )
            )
        )
        \\s*
*/
//new Regex(@"(?< switch> -{1,2}\S*)(?:[=:]?|\s+)(?< value> [^-\s].*?)?(?=\s+[-\/]|$)");
/*
    const KEEP_xre = XRegExp(`
#        (?<= \\s )  #leading white space (look-behind)
#        (?: ^ | \\s+ )  #skip leading white space (greedy, not captured)
        \\s*  #skip white space at start
        (?<argstr>  #kludge: need explicit capture here; match[0] will include leading/trailing stuff even if not capturing
            (
                (  #take quoted string as-is
                    (?: (?<quotype> (?<! \\\\ ) ['"] ))  #opening quote type; negative look-behind to skip escaped quotes
                    (
                        (?: . (?! (?<! \\\\ ) \\k<quotype> ))  #exclude escaped quotes; use negative lookahead because it's not a char class
                        .*?  #capture anything up until trailing quote (non-greedy)
                    )
                    (?: \\k<quotype> )  #trailing quote same as leading quote (not captured)
                )
            |
                (?<= \\\\ ) [\\s\\n\\#]  #or take escaped space/newline/"#" as regular chars; positive look-behind
            |
                [^\\s\\n\\#]  #or any other char
            )+  #multiple occurrences of above (greedy)
        )
        (?: \\s+ | \\# .* | $ )  #skip trailing white space or comment (greedy, not captured)
#        (?= \s )  #trailing white space (look-ahead)
        `, "gmx"); //"xy"); //"gx"); //sticky to prevent skipping over anything; //no-NOTE: sticky ("y") no worky with .forEach //"gxy"); //"gmxy");
//        (?: \\n | $ )
//    str.replace(/\s*#.*$/, ""); //strip trailing comment
//    return (which < 0)? [str]: str.split(" "); //split into separate args
//    return tostr(str).replace(COMMENT_xre, "").split(UNQUO_SPACE_xre).map((val) => { return val.unquoted || val}); //strip comment and split remaining string
//debug(`${"shebang str".cyan_lt}: '${str}'`);
//debug(!!"0");
*/
//    const QUO_STR = `\\\\ [^] | " (?: \\\\ " | [^"] )* " | ' (?: \\\\ ' | [^'] )* '`; //\\\\ ['"] //match escaped quotes or quoted strings; based on https://stackoverflow.com/questions/6462578/regex-to-match-all-instances-not-inside-quotes/23667311#23667311
    const matches = [];
//    for (var ofs = 0;;)
//    {
//        var match = XRegExp.exec(` ${tostr(str)}`, KEEP_xre); //, ofs, "sticky");
//        if (!match) break;
//    XRegExp.forEach(tostr(str), KEEP_xre, (match, inx) => matches.push(match.argstr)); //debug(`#![${inx}]: '${match[0]}' ${match.index}`); //no-kludge: exclude surrounding spaces, which are included even though non-captured; //`${match.quostr || match.barestr}`);
//debug(JSON.stringify(str.match(EXTRACT_xre)));
//    tostr(str).replace(SHEBANG_xre, (match, is_shebang, keep) => debug(match));
    tostr(str).replace(SHEBANG_xre, (match, is_shebang, keep) => keep? matches.push(keep): matches.ok = matches.ok || is_shebang); //debug(keep, `shebang arg ${matches.length}`)): "");
//    {
//        debug(`match[${inx}]:`.blue_lt, JSON.stringify(match), match.trimmed.quoted.cyan_lt); //, ${"quostr".cyan_lt} '${match.quostr}', ${"barestr".cyan_lt} '${match.barestr}'`);
//        matches.push(match.trimmed); //kludge: exclude surrounding spaces, which are included even though non-captured; //`${match.quostr || match.barestr}`); //
//        ofs = match.index + match[0].length;
//    }
//    });
debug("shebang args?", !!matches.ok, matches); //.join(", ".blue_lt));
//debugger;
    return matches.ok? matches: null;
}
module.exports.shebang_args = shebang_args;


//function is_shebang(chunk)
//{
//    return (this.linenum == 1) && chunk.match(/^\s*#\s*!/);
//}


////////////////////////////////////////////////////////////////////////////////
////
/// debug:
//

//const ISNT_ARRAY = {}; //allows in-line array duck typing instead of explicit "if" stmt using Array.isArray()

//debug output:
//if enabled, debug output is separated from preprocessor results (stderr vs stdout)
//wrapped as regular function to allow hoisting; CAUTION: if hoisted, must self-init on first call
//can be used in-line for easy debug (returns first arg)
function debug(...args)
{
    if (!debug.nested) debug_init(); //self-init for hoist
    const retval = args[0]; //.top; //return first value; allows in-line usage for easier debug
    if (!debug.enabled || !args.length) return (debug.depth = 0) || retval; //allow in-line debug() usage
//    const was_busy = debug.busy; //if (debug.busy) return retval; //avoid recursion (likely via XRE)
//    debug.busy = true;
//            if (/*!Array.isArray(debug.enabled)*/!debug.enabled.push) debug.enabled = []; //use array to
//console.error(`debug.enabled = ${JSON.stringify(debug.enabled)} ${srcline(+2)}`.cyan_lt);
    if (isNaN(++debug.depth)) debug.depth = 1; //skip self in caller stack
//    args = Array.from(arguments).shift_fluent()/*drop depth*/.push_fluent(srcline(depth));
//            args = Array.from(arguments).shift_fluent(); //drop depth arg
//            const has_color = args[args.length - 1].toString().match(ENDCOLOR_re) || [""]; //slice(-ENDCOLOR.length) == ENDCOLOR)? ENDCOLOR: "";
//            if (has_color[0]) args.push(args.pop().slice(0, has_color.index)); //-ENDCOLOR.length)); //move color after srcline
    for (let i = 1; i < args.length; i += 2) //kludge: unswap value + label; swap was likely due to in-line debug() retval
    {
//        if (XRE.busy) break; //kludge: avoid recursion
        const LABEL_xre = `
            (?<begin_color> ${ANSI_COLOR(true)} )?
            <: ${WHITE}?   #notation to move label ahead of value
            (?<label> ${ANYCHAR}+? )
            (?<end_color> ${ANSI_COLOR(false)} )?
            `/*.xre_tidy*/.anchorRE.XRE();
//console.error(typeof((args[i + 1] || ""), args[i], args[i + 1], srcline(1));
        const parts = tostr(args[i]).match(LABEL_xre); //.toString() no worky on undefined so just use "+"
        if (parts) args.splice(i - 1, 2, `${parts.begin_color || ""}${parts.label}:${parts.end_color || ""}`, args[i - 1]); //kludge: swap label and value for easier reading during debug
    }
    const ADDCOLOR_xre = `(?<has_color> ${ANSI_COLOR(true)} .* $ ) | (?<! ${ESC} ) (?<islabel> [?:] ) ${WHITE}? $`.XRE(); //label := string + punctuation
//apply decorations:
    args = args.map((arg, inx) => (tostr(arg).match(ADDCOLOR_xre) || {}).islabel? arg.pink_lt: (inx && (typeof arg == "string"))? `${arg.nocolors.length}:`.blue_lt + arg: arg); //highlight uncolored labels for easier debug
//    (/*XRE.busy? args.push:*/ args.push/*_colored*/)(srcline(debug.depth)); //(colorof(args, srcline(debug.depth))); //colorof(args))); //add src line info to show where it came from; *very* useful for debug
//debugger;
//const ENDCOLOR = "%".blue_lt.replace(/^.*%/, ""); //extract color-end control seq
//    args.push(ENDCOLOR + srcline(debug.depth)); //add src line info to show where it came from; *very* useful for debug; kludge: apply latest color to srcline
    args.push(colorof(args, srcline(debug.depth))); //add src line info to show where it came from; *very* useful for debug; kludge: apply latest color to srcline
//    args.push(srcline(depth) + remove_endcolor(args)); //+ ` has_c? ${!!has_color[0]}, #args ${args.length}, ecol len ${ENDCOLOR.length}, str len ${args[args.length - 1].toString().length}, encol ofs ${args[args.length - 1].indexOf(ENDCOLOR)}`);
//    let last_color;
//    const RESET_COLOR_re = /\x1b\[0m$/;
//    const ANY_COLOR_re = /\x1b\[[0-9;]+m/g;
//    if (/*Array.isArray*/ (debug.enabled || ISNT_ARRAY).push) debug.enabled.push(args); //CAUTION: assumes arg refs won't change before flush
//BROKEN:            else if (debug.enabled) console.error.apply(console, args.map((arg) => arg && (last_color = (arg.toString().match(ANY_COLOR_re) || [])[0] || last_color, escu(arg).toString().replace(RESET_COLOR_re, last_color || "$&")))); //args.map((arg) => arg.escall)); //NOTE: use stderr to keep diagnostics separate from preprocessor output (stdout)
//    else if (debug.enabled) console.error(...args.map((arg) => fmt(arg))); //args.map((arg) => arg.escall)); //NOTE: use stderr to keep diagnostics separate from preprocessor output (stdout)
//    if (debug.enabled) (/*(debug.enabled || ISNT_ARRAY)*/ Array.isArray(debug.enabled)? debug.enabled.push: console.error)(...args.map((arg) => fmt(arg)));
//    ((debug.enabled || {}).push || nop)(args.map((arg) => fmt(arg)));
//console.error(typeof debug.enabled, JSON.stringify(debug.enabled), srcline());
    debug.enabled.push(args); // /*XRE.busy? args:*/ args.map((arg, inx, all) => escnp(arg))); //, !inx || (inx == all.length - 1))); //CAUTION: don't ins len on srcline (messes up multi-collapse)
    debug.depth = 0; //auto-reset
//    debug.busy = false;
    return retval; //allow in-line debug() usage

//    function fmt(thing, hide_len) { return ((!hide_len && (typeof thing == "string"))? `${thing.nocolors.length}:`.blue_lt: "") + tostr(thing).escnp/*.escnl*/; } //((typeof thing == "object")? JSON.stringify(thing): thing.escnp).escnp.escnl; } //escnp((typeof thing != "string")? JSON.stringify(thing): thing); } //args.map((arg) => arg.escall))
}
module.exports.debug = debug;


//init buffering, add variants:
function debug_init()
{
    if (debug.nested) return; //first-time init only
//        module.exports.debug = debug;
//allow calller to enable/disable:
//use "[]" to enable buffering
    const save_enabled = isundef(debug.enabled, []); //array collects output until caller decides
    Object.defineProperty(debug, "enabled", //tri-state: true/false/[]
    {
//?            enumerable: true,
        get() { return /*this*/ debug.bufs; }, //TODO: debug.enabled.push()/pop()?
        set(onoff) //pass [] to enable buffering, or truey/falsey to turn on/off
        {
//console.error(`setting debug.enabled = ${typeof onoff}:${JSON.stringify(onoff)} ${srcline(1)}${srcline()}`.cyan_lt);
//console.error(typeof debug.bufs, typeof (debug.bufs || ISNT_ARRAY), srcline());
//            if (onoff && Array.isArray(debug.bufs) /*|| ISNT_ARRAY).forEach*/) debug.bufs.forEach((arglist) => console.error(...arglist)); //.map((arg) => fmt(arg)))); //.map((arg) => arg.escall))); //flush buffers; duck typing
            if (onoff) ((debug.bufs || {}).flush || nop)(); //flush in case buffering status is changing
//TODO: dedup multiple srclines across args:
            this.bufs = !Array.isArray(onoff)? onoff && {push: (arglist) => console.error(...arglist.map((arg) => escnp(arg, {arysep: ", ".blue_lt})))}: //on/off, no buffering
                Object.assign(onoff, {flush: () => onoff.forEach((arglist) => console.error(...arglist.map((arg) => escnp(arg, {arysep: ", ".blue_lt}))))});
//                Array.isArray(onoff)? {flush: Object.assign; //Array.isArray(onoff)? onoff: ; //? (this.bufs || []): null; //turn buffering on/off
        },
    });
    debug.enabled = save_enabled; //[]; //tri-state: array collects output until caller decides
    nodeCleanup((/*code, signal*/) => debug.enabled = true); //flush saved output
//append args to previous debug entry:
    debug.more =
    function debug_more(...args)
    {
        const retval = args[0]; //.top; //return first value; allows in-line usage for easier debug
        if (!debug.enabled || !args.length) return retval;
//        if (debug_more.busy) return retval; //avoid recursion (likely via XRE)
//        debug_more.busy = true;
//            else if (/*Array.isArray*/ (debug.enabled || {}).top)
        if (!Array.isArray(debug.enabled /*|| ISNT_ARRAY).push*/) || !debug.enabled.length) fatal("debug.more: not allowed without buffering"); //console.error.apply(console, args); //NOTE: use stderr to keep diagnostics separate from preprocessor output (stdout)
//            const debtop = debug.enabled.top;
        //(?:x)  non-capturing match
        //x(?=y)  positive lookahead
        //x(?!y)  negative lookahead
        //(?<=y)x  positive lookbehind
        //(?<!y)x  negative lookbehind
        //(?: . (?! (?<! \\\\ ) \\k<quotype> ))  #exclude escaped quotes; use negative lookahead because it's not a char class
//        const debug_latest = debug.enabled.top; //[debug.enabled.length - 1];
//todo        const color_preserve = [remove_endcolor(args), remove_endcolor(debug_latest)].reduce((found, str) => found || str, ""); //use first one, but remove both
//        debug.enabled.top.splice(-1, 0, ...args.map((arg) => (typeof arg == "string")? `${arg.length}:`.blue_lt + arg: arg)); //insert args ahead of trailing srcline
        debug.enabled.top.splice(-1, 0, ...args); //insert args ahead of trailing srcline
//console.error("deb latest", JSON.stringify(debug_latest));
//            let latest_srcline = debug_latest.pop();
//            const has_color = latest_srcline.match(ENDCOLOR_re) || [""]; //slice(-ENDCOLOR.length) == ENDCOLOR)? ENDCOLOR: "";
//console.error("more-1", has_color[0].escall);
//            if (has_color[0]) latest_srcline = latest_srcline.slice(0, has_color.index); //-ENDCOLOR.length); //move color after srcline
//console.error(escnp(debug.enabled.top.top, false), srcline());
//console.error(escnp(nocolors(debug.enabled.top.top), false), srcline());
//console.error(escnp(colorof(debug.enabled.top), false), srcline());
        const latest_srcline = multi_srcline(nocolors(debug.enabled.top.pop()), srcline(+1)); //`${nocolors(debug.enabled.top.pop())},${srcline(+1)}`.replace(DEDUPFILE_xre, "$<first_file>:$<first_line>:$<second_line>"); //add additional srcline, coalesce dupl file names; kludge: +1 nesting level
//console.error("latest srcline", latest_srcline.escall);
//console.error("has c", has_color[0].escall);
//        debug_latest.join("")
//console.error(escnp(latest_srcline, false), srcline());
//console.error(escnp(colorof(debug.enabled.top, latest_srcline), false), srcline());
        debug.enabled.top.push/*_colored*/(colorof(debug.enabled.top, latest_srcline)); //(colorof(debug.enabled.top, latest_srcline)); //+ color_preserve); //has_color[0]);
//        debug_more.busy = false;
        return retval; //allow in-line debug() usage
    };
//output 1x only:
    debug.once =
    function debug_once(...args)
    {
        const key = srcline((debug.depth || 0) +1); //tostr(args[0]); //CAUTION: only checks first arg
        if (key in debug.seen) return debug.seen[key];
//            if (!args.top.match(/@[^\/<>|:&]+:\d+$/)) args.push(`1x${srcline(1)}`);
        return debug.seen[key] = debug.nested(+2, ...args);
    }; //CAUTION: ";" must be here else following line will be appended
    debug.seen = {};
//nested variants:
    debug.nested =
    function debug_nested(depth, ...args) { debug.depth = depth; return debug(...args); }
    debug.once.nested =
    function debug_nested_once(depth, ...args) { debug.depth = depth; return debug.once(...args); }
//    return debug.nested(+1, ...args); //insert depth arg
}


/*
//wrapper for real debug function:
//NOTE: Array.isArray throws on non-objects so use duck typing instead
//TODO: create debug output /xform stream?
const debug =
module.exports.debug =
function debug(args)
{
    if (!debug.nested) throw `debug(): hoisting error`.red_lt;
    return debug.nested.apply(debug, unshift_fluent(Array.from(arguments), +1)); //insert depth arg
//    debug.depth = 0; //reset for next time
}
Object.defineProperty(debug, "enabled",
{
    enumerable: true,
    get() { return this.bufs; }, //TODO: debug.enabled.push()/pop()?
    set(onoff) //pass [] to enable buffering
    {
//console.error(`debug.enabled <- ${typeof onoff} ${JSON5.stringify(onoff)} ${srcline()}`.blue_lt);
//console.error(JSON5.stringify(this.bufs, null, "  "), srcline());
        if (/-*Array.isArray*-/ (this.bufs || {}).forEach) this.bufs.forEach((args) => console.error.apply(console, args)); //flush buffers; duck typing
        this.bufs = onoff; //Array.isArray(onoff)? onoff: ; //? (this.bufs || []): null; //turn buffering on/off
    },
});
debug.enabled = []; //collect output until caller decides
//real debug function:
//"depth" compensates for nested calls
//Object.defineProperty(debug, "nested", //prevent accident overwrite
debug.nested =
function debug_nested(depth, args)
{
    if (!debug.enabled) return;
//    console.error.apply(console, shift_fluent(push_fluent(Array.from(arguments), srcline(depth))); //NOTE: stderr keeps diagnostics separate from preprocessor output (stdout)
//    return debug_nested; //fluent
//    if (isNaN(++depth)) depth = 1;
    ++depth || (depth = 1);
//    args = Array.from(arguments).shift_fluent()/-*drop depth*-/.push_fluent(srcline(depth));
    args = Array.from(arguments); //push_fluent(shift_fluent(Array.from(arguments)), srcline(depth)); //exclude depth, append srcline info
    const ENDCOLOR = "%".red.replace(/^.*%/, "");
    if (args.top.toString().slice(-ENDCOLOR.length) != ENDCOLOR) args.push(srcline(depth));
    else args.top = args.top.slice(0, -ENDCOLOR.length) + srcline(depth) + args.top.slice(-ENDCOLOR.length); //preserve color on srcline
//if (!Array.isArray(args)) throw "bad ary".red_lt;
    if (/-*Array.isArray*-/ (debug.enabled || {}).push) debug.enabled.push(args); //CAUTION: assumes arg refs won't change before flush
    else console.error.apply(console, args); //NOTE: use stderr to keep diagnostics separate from preprocessor output (stdout)
}
//append args to previous debug entry:
debug.more =
function debug_more(args)
{
    if (!debug.enabled) return;
    else if (/-*Array.isArray*-/ (debug.enabled || {}).top)
    {
        const debtop = debug.enabled.top;
//(?:x)  non-capturing match
//x(?=y)  positive lookahead
//x(?!y)  negative lookahead
//(?<=y)x  positive lookbehind
//(?<!y)x  negative lookbehind
//(?: . (?! (?<! \\\\ ) \\k<quotype> ))  #exclude escaped quotes; use negative lookahead because it's not a char class
        const DEDUPFILE_xre = XRegExp(`
            (?: ^ | , ) \\s*  #delimeter
            (?<first_file> [^:]+ ) : (?<first_line> [^,]+ ) ,  #first srcline()
            \\k<first_file> : (?<second_line> [^,]+ )  #second srcline()
            `, "gx");
        debtop.splice.apply(debtop, splice_fluent(Array.from(arguments), 0, 0, -1, 0)); //insert args ahead of trailing srcline(); CAUTION: assumes extensions() already called
        debtop.top = `${debtop.top},${srcline(+1)}`.replace(DEDUPFILE_xre, "$<first_file>:$<first_line>:$<second_line>"); //add additional srcline, coalesce dupl file names; kludge: +1 nesting level
    }
    else throw `debug.more: buffering not enabled ${srcline()}`.red_lt; //console.error.apply(console, args); //NOTE: use stderr to keep diagnostics separate from preprocessor output (stdout)
}
*/
//debug.enabled = []; //collect output until debug option is decided
//debug_nested(0, "hello 0");
//debug_nested(1, "hello 1");
//debug_nested(2, "hello 2");
//debug("hello");

//CaptureConsole.startCapture(process.stdout, (outbuf) => { debug("regurge:", outbuf.replace(/\n/g, "\\n")); }); //include any stdout in input
//console.error("test1");
//console.log("test2");
//CaptureConsole.stopCapture(process.stdout);

//var ary = [];
//ary.push("line 1".red_lt);
//ary.push("line 2");
//ary.push("line 3".green_lt);
//console.error("test 1", ary.join("\n"));
//console.error("test 2", ary.join("\n").cyan_lt);
//console.error("test 3", ary.join("\n").cyan_lt.color_preserve);
//process.exit(0);

//https://stackoverflow.com/questions/7376238/javascript-regex-look-behind-alternative
//use negative lookahead instead:   (?<!filename)\.js$   ==>  (?!.*filename\.js$).*\.js$
//const CommentsNewlines_re = /(?<![\\])#.*\n|\n/g;  //strip comments + newlines in case caller comments out parent line
//console.error(`test '${quostr("test").replace(/\t/g, "\\t").replace(/\n/g, "\\n")}'`.yellow_lt);

/*
const xre_test = XRegExp(`
    ^ \\s*  #start of string (leading white space should already have been skipped)
    ${quostr("inner")}  #optionally quoted string
#    (?<quotype1> ['"]) (?<inner> .*) \\k<quotype1>
    ( \\s* ; )?  #optional trailing ";"
    \\s* $  #ignore trailing white space
    `.replace(CommentsNewlines_re, ""), 'xi');
//console.error("here1".cyan_lt);
var test = " 'a \"string' ".match(xre_test);
if (!test) test = {quote: "NOPE", inner: "NOPE"};
console.error("match1?".cyan_lt, JSON5.stringify(test), `#${test.quotype2}#`, `#${test.inner}#`);
test = "\"this is \\\"another 'string'\"".match(xre_test);
console.error("match2?".cyan_lt, JSON5.stringify(test), `#${test.quotype2}#`, `#${test.inner}#`);
//process.exit(0);
*/

//debugger;
//console.log(JSON5.stringify(eval("'hi,' + ' there'")));
//const re_test = XRegExp(`(?<year>[0-9]{4} ) -?  # year
//          (?<month>[0-9]{2} ) -?  # month
//          (?<day>[0-9]{2} )     # day`, 'x');
//const result = "2015-01-02".match(re_test); //XRegExp.exec("2015-01-02", re_test);
//console.log(`match yr ${result.year}, mon ${result.month}, day ${result.day}, result ${JSON5.stringify(result)}`.blue_lt);
//console.log(`re ${JSON5.stringify(re_test)}`.blue_lt);
//process.exit(0);


////////////////////////////////////////////////////////////////////////////////
////
/// Extensions:
//

//require("magic-globals"); //__file, __line, __stack, __func, etc
//require("colors").enabled = true; //for console output; https://github.com/Marak/colors.js/issues/127
function extensions()
{

//make JSON a little easier to read (for debug):
//    [JSON.stringify, JSON.saved_stringify] = [function(...args)
//    {
//var test_val0 = JSON.doing_stringify;
//var test_val1 = ++JSON.doing_stringify;
//var test_val2 = ++JSON.doing_stringify? "yes": "no";
//console.error(typeof test_val0, test_val0, typeof test_val1, test_val1, typeof test_val2, test_val2);
//        if (++JSON.doing_stringify) return sv_json_stringify.apply(JSON, arguments); //JSON5 uses JSON; avoid infinite recursion
//        JSON.doing_stringify = 0;
//        return (tostr(JSON5.stringify.apply(JSON5, arguments)).replace(/,(?=\w)/gi, ", ").replace(/:/g, ": "); //put a space after ",:" for easier readability
//        const want_fixup = (arguments.length < 2) && "replace"; //leave as-is if caller is using custom fmter
//        if (JSON.busy) return JSON.saved_stringfy(...args);
//        JSON.busy = true;
//        const retval = tostr(JSON.stringify(...args))
//            .replace(/"(\w+)":/g, want_fixup? "$1: ": "$1:") //remove quotes from key names, put space after if no fmter passed in
//            /*.replace*/ [want_fixup || "nop_fluent"](/,(?=\w)/gi, ", "); //also put a space after "," for easier readability
//            .replace(/,(?="?\w)/gi, ", ") //also put a space after "," for easier readability
//            .replace(/"(?!\d)(\w+)":/g, "$1: ".blue_lt); //remove quotes from key names, put space after if no fmter passed in
//    return tostr(str).replace(/(\{)"|(,)"|"(:)/g, "$1$2$3"); //|#PEG-KLUDGE#\}/g, "$1$2$3"); //kludge: peg parser wants matched "}" here
//        JSON.busy = false;
//        return retval;
//    }, JSON.stringify]; //CAUTION: ";" must be here else following line will be appended

    Object.defineProperties(global,
    {
//        __srcline: { get: function(depth) { return srcline((depth || 0) +1); }, },
        __srcline: { get() { return srcline(+1); }, },
        __parent_srcline: { get() { return srcline(+2); }, },
        __mystack: { get() { return __stack.filter((frame) => (pathlib.basename(frame.getFileName() || "????") == `${__file}.${__ext}`)); }, }, //only look at my functions
    });

//use debug.once instead:
//console.once = function(...args)
//{
//    const key = srcline(+1); //args[0];
//    if (!this.seen) this.seen = {};
//    if (++this.seen[key.toString()]) return; //CAUTION: only checks first arg
//    if (!args.top.match(/\w+:\d+$/)) args.push(`1x${srcline(1)}`);
//    console.error.apply(null, args.map((arg) => escu(arg)));
//    this.seen[key = 1;
//};

//process:
    process.hrtime.bigint =
    function hrtime_bigint()
    {
        const [sec, nsec] = process.hrtime();
        return sec * 1e9 + nsec;
    }; //CAUTION: need ";" here to prevent following line from being appended

    Object.defineProperties(Array.prototype,
    {
//props (parameterless functions):
        top:
        {
            get() { return this[this.length - 1]; }, //NOTE: will be undefined when array is empty
            set(newval) { if (!this.length) this.push(); this[this.length - 1] = newval; }, //return this; },
//        enumerable: true,
        },
        toppp: //top prior to latest push(); read-only (no setter) - if stack is empty, don't know what top element should be
        {
            get() { return this[this.length - 2]; }, //NOTE: will be undefined when array is empty
//n/a            set(newval) { if (!this.length) this.push(); this[this.length - 1] = newval; }, //return this; },
//        enumerable: true,
        },
//methods:
        at: { value: function(inx) { return this[((inx < 0) && this.length) + (inx % this.length)]; }, }, // (inx < 0)? this.length + inx: inx]; }, }, //this.slice(inx, inx + 1)[0]; }, }, //(inx < 0)? }} //NOTE: inx can be negative; wraps around
        nop: { value: function() { return this; }, }, //pass-thru method for inactve branch of "?:"
        forEachTry: { value: function(cb, thisArg) { cb_try.cb = cb; return this.forEach(cb_try, thisArg); }, },
//        push_colored: { value: function(str) { return this.push(colorof(this, str)); }, },
//[/*plurals, plurales,*/ join_flush, push_fluent, pop_fluent, shift_fluent, unshift_fluent, splice_fluent].forEach((method) => //.split
        unshift_fluent: { value: function(...args) { this.unshift(...args); return this; }, },
        splice_fluent: { value: function(...args) { this.splice(...args); return this; }, },
        push_fluent: { value: function(...args) { this.push(...args); return this; }, },
        pop_fluent: { value: function(...args) { this.pop(...args); return this; }, },
    });

//    let fix_this = 0;
    Object.defineProperties(String.prototype,
    {
//props (parameterless functions):
//NOTE: fat arrow (lamba) functions are supported in getters: https://stackoverflow.com/questions/33827519/es6-getter-setter-with-arrow-function
        quoted: { get() { return quote(this/*.toString()*/); }, },
//    quoted1: { get() { return quote(this/*.toString()*/, "'"); }, },
        unquoted: { get() { return unquote(this/*.toString()*/); }, },
//    unparen: { get() { return unparen(this/*.toString()*/); }, },
//    unquoescaped: { get() { return unquoescape(this/*.toString()*/); }, },
        unindent: { get() { return unindent(this); }, },
//        spquote: { get() { return spquote(this); }, },
        escnp: { get() { return escnp(this); }, },
//        escnl: { get() { return escnl(this); }, },
        unesc: { get() { return unesc(this); }, },
        noblanks: { get() { return noblanks(this); }, },
        anchorRE: { get() { return anchorRE(this/*.toString()*/); }, },
        unanchorRE: { get() { return unanchorRE(this/*.toString()*/); }, },
        nocolors: { get() { return nocolors(this/*.toString()*/); }, },
        color_fixup: { get() { return color_fixup(this/*.toString()*/); }, },
//        xre_tidy: { get() { return xre_tidy(this); }, },
//    xre_tidy: { get: () => xre_tidy(this), }, //get() { return xre_tidy(this); }, },
//methods:
        nop: { value: function() { return this; }, }, //pass-thru method for inactve branch of "?:"
        XRE: { value: function(flags) { return XRE(this, flags); }, }, //console.error(JSON.stringify(this), srcline(+1), srcline()); return new XRegExp(this, flags || "x"); }, },
//NOTE: XRegExp.exec works with non-XRegExp RE also; these overrides allow XRegExp to work in place of RE (mainly named captures):
        match: { value: function(...args) { return XRegExp.exec(this, ...args); }, }, //xre_fixup(xre, XRegExp.exec(this, xre)); }; //console.error("is xregexp? " + XRegExp.isRegExp(re)); return XRegExp.exec(this, re); } //XRegExp.isRegExp(re)? XRegExp.exec(this.toString(), re): this.sv_match(re); }
//TODO: matchAll: //https://2ality.com/2018/02/string-prototype-matchall.html
//CAUTION: replace() ignores "g" flag if replacement is a string; use replaceAll()
        replace: { value: function(...args) { if (!XRegExp.isRegExp(args[0]) && (args.top !== "!global") && (pathlib.basename(__stack[1].getFileName()) == __file)) /*if (++fix_this > 10) fatal(); else*/ warn(`str replace '${args[0]}' in ${pathlib.basename(__stack[1].getFileName())} !global ${srcline(+1)}`); return XRegExp.replace(this, ...args); }, }, //warn about !global replace unless caller explicitly overrides; TODO: use XRegExp.forEach?
//        replacex: { value: function(from, to) { return XRegExp.replace(this, from, to, XRegExp.isRegExp(from) && from.want_scope); }, }, //&& ~(from.flags || from.xregexp.flags).indexOf("g"))? 'all': 'one'); }, }, //TODO: use XRegExp.forEach?
        replaceAll: { value: function(from, to) { return this.replace(togrex(from), to || ""); }, },
    });

//emit event after returning:
//allows caller to set up event handlers before event fires
//function emit_fluent_delayed(evt, ...args)
//{
//debug("emit fluent", evt, JSON5.stringify(data));
//no    this.emit(evt, data); //kludge: allow caller to install event handlers before firing event
//    process.nextTick(() => this.emit(evt, ...args)); //kludge: return and allow caller to install event handlers before firing event
//    return this; //fluent
//}
//EventEmitter.prototype.emit_fluent_delayed = function(...args) { return emit_fluent_delayed.call(this, ...args); }; //CAUTION: ";" must be here or else following line is appended
//EventEmitter.prototype.emit_fluent_delayed = function(...args) { process.nextTick(() => this.emit(...args)); return this; }
    Object.defineProperties(EventEmitter.prototype,
    {
        emit_fluent_delayed: { value: function(...args) { process.nextTick(() => this.emit(...args)); return this; }, },
        pushline: { value: function(str) { /*if (str)*/ this.push(`${escu(str).escnp/*.color_fixup*/}\n`); }, }, //maintain correct line#
    });
}


////////////////////////////////////////////////////////////////////////////////
////
/// Helper functions:
//

//check if msg has a "type":
function msgtype(msg)
{
    const MSGTYPE_xre = `^ (?: ${ANSI_COLOR(true)} )* (?<label> \\[ [^\\]]+ \\] )`.XRE(); //allow nested colors at start
    const parts = tostr(msg).match(MSGTYPE_xre); // /^\[[^\]]+\]/); //check for msg label/type
    return (parts || {}).label;
}

//show warning message:
//returns undef so caller can use for return
function warn(msg) //, limit)
{
//    if (isNaN(++warn.count)) warn.count = 1;
    ++warn.count || (warn.count = 1);
//    if (limit)
//    {
//        if (!warn.seen) warn.seen = {};
//        if (++warn.seen[msg] > limit) fatal();
//        else if (!warn.seen[msg]) warn.seen.msg = 1;
//    }
//    const parts = tostr(msg).match(MSGTYPE_xre); // /^\[[^\]]+\]/); //check for msg label/type
//    console.error(`${!parts? "[WARNING] ": ""}${escu(msg)} ${srcline(1)}`.yellow_lt.color_fixup);
    console.error(multi_srcline(`${!msgtype(msg)? "[WARNING] ": ""}${escu(msg)} ${srcline(1)}`).yellow_lt.color_fixup);
}
module.exports.warn = warn;


//show error message:
//returns undef so caller can use for return
//NOTE: does not stop execution
function error(msg)
{
//    throw `${msg || "error"}  @${__parent_line}`.red;
//    if (isNaN(++error.count)) error.count = 1;
    ++error.count || (error.count = 1);
//    const parts = tostr(msg).match(MSGTYPE_xre); // /^\[[^\]]+\]/); //check for msg label/type
//    error.nested = error.nested || 0;
    console.error(multi_srcline(`${!msgtype(msg)? "[ERROR] ": ""}${escu(msg)} ${srcline(1)}`).red_lt.color_fixup); //${multi_srcline(+4, +3, +1, +2)}
    error.nested = 0; //auto-reset for next time
}
module.exports.error = error;


//show error + quit:
function fatal(msg)
{
//    ++srcline.nested;
//    const parts = tostr(msg).match(MSGTYPE_xre); // /^\[[^\]]+\]/); //check for msg label/type
//    ++srcline.nested || (srcline.nested = 1);
    error(`${!msgtype(msg)? "[FATAL] ": ""}${escu(msg || "fatal exit")} ${srcline(1)},`);
//    console.trace("call stack:");
    console.error(__stack.filter(isMyStackFrame).map((stkfr, depth, all) => `${"  ".repeat(all.length - depth)}${stkfr.getFunctionName() || "<unnamed>"}() @${pathlib.basename(stkfr.getFileName() || "<anon>")}:${stkfr.getLineNumber() || 0}`).join("\n").red_lt.color_fixup); //stk[${depth}/${all.length}]
//    console.error(typeof __stack, Array.isArray(__stack)); //__stack.split("\n"));
    process.exit();

    function isMyStackFrame(stkfr) { return stkfr.getFunctionName() || (stkfr.getFileName() == __file); }
}
module.exports.fatal = fatal;


//wrap a callback in try..catch:
//useful for array.forEach(), string.replace(), etc (exceptions are not reported)
function cb_try(...args)
{
    try { return cb_try.cb(...args); }
    catch (exc) { error(`[EXC] ${exc} ${srcline(+1)}`); }
}


//convert string to readable stream:
//based on https://stackoverflow.com/questions/12755997/how-to-create-streams-from-string-in-node-js
function str2strm(str)
{
//debug(str.replace(/\n/g, "\\n"));
    const strm = new Readable();
    strm._read = function(){}; //kludge: need to define this for Readable stream
    strm.push(str);
    strm.push(null); //eof
//if (!i ) { strm.pipe(fs.createWriteStream("dj.txt")); continue; }
    return strm;
}


//tag or untag a char/str:
//Unicode upper byte holds tag, original char is left as-is in lower byte; chars tagged with 0 == original (ASCII) char
//Unicode is used so string len/indices don't change
//NOTE: thiw won't work if source stream contains Unicode chars; in that case, go back to using "[(){}])#\d" for tags
function TAGCHAR(str, tag)
{
//Javascript regex handles Unicode okay:
//    const str = "abc\u1234def\u1000ghi\u2000jkl\u0999xyz";
//    const re = /[\u1000-\u1fff]/g;
//    console.error(str.length, str.replace(re, (char) => `%x${char.charCodeAt(0).toString(16)}%`.green_lt).replace(/[\u0100-\uffff]/g, (char) => `%x${char.charCodeAt(0).toString(16)}%`.red_lt));
//    process.exit();
//    if (chr.length == 1) return chr.charCodeAt(0)
//    const FIND_re = /[\u0100-\uffff]/g; //gu; // /(?:[(){}])#\d+/g;
//debugger;
    if (!tag) return tostr(str).replace(UNICODE_re, (chr) => String.fromCharCode(chr.charCodeAt(0) & 0xFF)); //untag
    if (tag < 0) return tostr(str).replace(UNICODE_re, (chr) => String.fromCharCode(chr.charCodeAt(0) - 0x100)); //promote tags
    tag = (tag || 0) << 8; //put tag in upper byte of Unicode char
//    if (!TAGCHAR.FIND_re) TAGCHAR.FIND_re = /[\u0100-\uffff]/g; //gu; // /(?:[(){}])#\d+/g;
//if (tag || chr.match(TAGCHAR.FIND_re)) debug(`tagchar(0x${chr.charCodeAt(0).toString(16)}, ${tag >> 8}):`, `${chr.length}:${chr.replace(TAGCHAR.FIND_re, (tagged) => String.fromCharCode(tagged.charCodeAt(0) & 0xFF).cyan_lt)}`, srcline(1), srcline(2));
//    return tostr(str).split("").map((chr) => String.fromCharCode((chr.charCodeAt(0) & 0xFF) | tag)).join(""); //`${chr}#${tag}
//    const ANYCHAR_re = /[^]/g; //init order problem; repeat here
    return tostr(str).replace(/[^]/g, (chr) => String.fromCharCode((chr.charCodeAt(0) & 0xFF) | tag)); //.join(""); //`${chr}#${tag}`
}


//return "file:line#":
//mainly for debug or warning/error messages
//optional depth to show ancestor
function srcline(depth, want_func)
{
    const want_path = (depth < 0);
//    const want_next = (depth === 99);
//    if (isNaN(++depth)) depth = 1; //skip this function level
//if (srcline.nested !== 0) console.error(JSON.stringify(__stack));
//broken    const frame = __stack[Math.abs(depth || 0) + srcline.nested + 1]; //skip this stack frame
//    srcline.nested = 0; //auto-reset
    const new_depth = (Math.abs(depth || 0)) + (srcline.nested || 0) + 2; //+1 for globals.get __mystack() +1 for globals.get __stack()
//    const CONTINUE = false, BREAK = true;
    const new_srcline = `@${__file}${frdesc(__mystack[new_depth])}`;
//console.error(...__stack.map((frame) => `${pathlib.basename(frame.getFileName() || "????")} vs. ${__file}.${__ext}`), __fili);
//if (!__mystack.length) { console.error("no my stack?"); process.exit(); }
    return new_srcline;
/*
    depth = Math.abs(depth || 0);
    for (;;)
    {
        const frame = __stack[++depth]; //skip over current stack frame to get caller
        if (!frame) return "@???:?"; //ran out of stack frames?
        if (!frame.getFileName) continue; //invalid stack frame?  not sure why this is necessary
        if (srcline.nested-- > 0) continue; //caller wants ancestry; NOTE: condition is false for undef/isNaN, which is good
        srcline.nested = 0; //auto-reset for next time
//console.error(`filename ${frame.getFileName()}`);
        const filename = (want_path? nop: pathlib.basename)(frame.getFileName() || "<none>", ".js"); //.unquoted || frame.getFileName();
//        const retval = `@${filename}${want_func? `(${frame.getFunctionName()})`: ""}:${frame.getLineNumber()}`; //.gray_dk; //.underline;
        const retval = `@${filename}${frdesc(frame)}`; //.gray_dk; //.underline;
if (new_srcline != retval) console.error(`srcline(${depth}) mismatch: new ${new_srcline} vs. old ${retval}`.red_lt, __mystack.length, __mystack.map((frame) => frdesc(frame)).join("->"), __srcline.red_lt);
        return new_srcline;
        return retval;
//    return `@${pathlib.basename(__stack[depth].getFileName(), ".js")}:${__stack[depth].getLineNumber()}`;
    }
*/
    function frdesc(fr)
    {
        if (!fr) fr = {getFunctionName: () => "none", getLineNumber: () => "??"};
        return (want_func? `(${fr.getFunctionName() || "anon"})`: "") + ":" + fr.getLineNumber();
    }
}
//srcline.nested = 0;
module.exports.srcline = srcline;


//return multiple srclines:
function multi_srcline(...args)
{
//XRE.debug = true;
//    const DEDUPFILE_xre = `
//        (?: ^ | , ) ${WHITE}?  #separator
//        (?<first_file> [^:]+ ) : (?<first_line> [^,]+ ) , ${WHITE}?  #first srcline()
//        \\k<first_file> : (?<second_line> [^,]+ )  #second srcline()
//        `/*.xre_tidy*/.XRE("gx");
//const SRCLINE_xre = `(?<file> .*? ) : (?<line> ${NUMBER} ) (?: \\. (?<column> ${NUMBER} ) ) `.anchorRE.XRE(); //split(":");
//overlapping RE matches no worky :(    const DEDUPFILE_xre = `
//        (?<keep_prefix>
//            (?: ^ | , ) ${WHITE}?  #separator
//            (?<filename> [^:]+? ) (?: [:.] ${WHITE}? ${NUMBER} )*  #first (group of) srcline(s)
//        )
//        , ${WHITE}?  \\k<filename>  #redundant info
//        (?<keep_suffix> : ${WHITE}? ${NUMBER} )  #useful part of second srcline
//        `/*.xre_tidy*/.XRE("gx");
//    const DEDUPFILE_xre = `
//        (?: ^ .*? ) ( , ${WHITE}? )? (?<filename> [^:]+? ) : ${NUMBER}
//        `/*.xre_tidy*/.XRE("gx");
//XRE.debug = true;
//TODO: check for junk between srclines + reset:
    const MULTI_SRCLINE_xre = `${WHITE}?${(SRCLINE_xre.xregexp.raw_src || SRCLINE_xre.xregexp.source).unanchorRE}`.XRE("gx");
//debug("xre:", MULTI_SRCLINE_xre.xregexp.source);
    const previous = [""];
    return args.map((arg) => !isNaN(arg)? srcline(arg + 1): arg) //kludge: +1 nesting level
        .join(",") //append additional srcline(s)
        .replace(MULTI_SRCLINE_xre, (match, file, line) => (file == previous.push_fluent(file).toppp)? `:${line}`: match); //dedup file names; NOTE: need a cbfunc for "g" flag to work
//        .replace(DEDUPFILE_xre, (match) => `${match.first_file}:${match.first_line}:${match.second_line}`); //drop dupl file names; NOTE: need a cbfunc for "g" flag to work
//        .replaceAll(DEDUPFILE_xre, "$<first_file>:$<first_line>:$<second_line>"), "<: after"); //drop dupl file names
}


//dedup multiple srcline:
function srcline_dedup(str)
{
    const MULTI_SRCLINE_xre = (SRCLINE_xre.xregexp.raw_src || SRCLINE_xre.xregexp.source).unanchorRE.XRE("gx");
    return tostr(str).replace(MULTI_SRCLINE_xre, (match, file, line) => (file == previous.push_fluent(file).toppp)? line: match); //dedup file names; NOTE: need a cbfunc for "g" flag to work
}

//make output language-neutral:
//replaces "//" C/JS-style comments with "#if 0".."#endif"
function language_neutral(str, want_linenums)
{
//    startup_code.comment = function(wanted) //turn comment on/off if needed
//    {
//        const has_comment = Array.prototype.join.call(this, "\n").match(/^#if 0(?![\s\S]*^#endif)/gm);
//        debug(`stup comment wanted? ${!!wanted}, has? ${!!has_comment}, ins? ${(!has_comment != !wanted)? wanted? "#if0": "#endif": ""}`);
//        if (!has_comment != !wanted) Array.prototype.push.call(this, wanted? "#if 0": "#endif");
//    }
//    startup_code.push = function(...args) { this.comment(true); return Array.prototype.push.apply(this, args); }
//    startup_code.pushexe = function(...args) { this.comment(false); return Array.prototype.push.apply(this, args); }
//    startup_code.join = function(...args) { this.comment(false); return Array.prototype.join.apply(this, args); }
//    startup_code.pop_fluent = function() { this.pop(); return this; }
//debug("ary", JSON.stringify(str));
//debug(JSON.stringify(str));
    const isary = Array.isArray(str) && "nop"; //multi-line handler only needed for array
//debug(typeof tostr(str)[isary || "split"], tostr(str)[isary || "split"].toString());
    return (isary? str: tostr(str).split(NEWLINE_re)).map(fixup).slice(!want_linenums? -1: 0)[isary || "join"]("\n");

    function fixup(linebuf, inx, all)
    {
//debug(typeof linebuf, linebuf, inx, all.length);
        const want_comment = !linebuf.indexOf("//"); //just check start of line; if it occurs mid-line then caller really wanted it
        if (!want_linenums)
        {
            if (!inx) fixup.commented = {true: [], false: []};
            fixup.commented[want_comment].push(linebuf);
            if (inx != all.length - 1) return;
//group commented lines first and wrap with "#if 0...#endif":
            const num_comments = fixup.commented[true].length;
            fixup.commented[true].forEach((line, i) => all[i + 0] = (!i? "#if 0\n": "") + line.slice(2));
            fixup.commented[false].forEach((line, i) => all[i + num_comments] = ((!i && num_comments)? "#endif\n": "") + line);
//debug("grouped ary", JSON.stringify(str));
            return all.join("\n");
        }
        if (want_comment && !fixup.has_comment)
        {
            if (inx == all.length - 1) linebuf += "\n#endif"; //exit in clean state
            else fixup.has_comment = true;
            return "#if 0\n" + linebuf;
        }
        if (!want_comment && fixup.has_comment)
        {
            fixup.has_comment = false;
            const linenum = want_linenums? `#line ${inx + 1}\n`: "";
            return `#endif\n` + linenum + linebuf; //preserve line#s; don't need +2 here because inx is already the correct line# (0-based)
        }
        if ((inx == all.length - 1) && fixup.has_comment) { linebuf += "\n#endif"; fixup.has_comment = false; } //reset state @eof
        return linebuf;
    }
}


////////////////////////////////////////////////////////////////////////////////
////
/// Utility functions:
//

//esc Unicode chars:
//prevents junk chars going to screen or output
//optional color highlight
function escu(str, want_color = true)
{
//    if (typeof str != "string") return str;
    return tostr(str).replace(/[\u0100-\uffff]/g, (uchar) =>
    {
//        const escaped = `\\u${("000" + uchar.charCodeAt(0).toString(16)).slice(-4)}`;
        const escaped = `\\u${uchar.charCodeAt(0).toString(16).padStart(4, "0")}`;
        return (want_color === 2)? ("\\" + escaped): (want_color/* !== false*/)? escaped[(typeof want_color == "string")? want_color: "blue_lt"]: escaped;
    });
//    return want_color? retval.cyan_lt: retval;
}


//make a string safe for use in regex pattern:
//allow caller to designate additional chars to be escaped, or all chars, or double escape
function escre(str, want_all) //, more)
{
    if (want_all && (typeof want_all != "string")) return tostr(str).replace(/[^]/g, (ch) => ((want_all == 2)? '\\\\': '\\') + (ch || 's+')); //(ch? '$&': 's+'));
//allow caller to treat extra chars as special RE char to be escaped:
//    return tostr(str).replace(new RegExp(`[.*+\\-?^$|{}()[\\]\\\\${tostr(want_all).replace(/[^.*+\\-?^$|{}()[\\]\\\\]/g, "\\$&")}]`, "g"), (ch) => `\\${ch? '$&': 's+'}`); //+ tostr(more).replace(/[\s\S]/g, "\\$&").join("");
//    return tostr(str).replace(new RegExp(`[-+.*?^$|{}()[\\]\\\\${tostr(want_all).replace(/[-\\]\\\\]/g, "")}]`, "g"), (ch) => "\\" + (ch || "s+")); //ch? "\\$&": "\\s+"); //+ tostr(more).replace(/[\s\S]/g, "\\$&").join("");
    return tostr(str).replace(new RegExp(`[${/*dedupe*/("-+.*?^$|{}()[]\\" + tostr(want_all)).replace(/[\^\-\]\\]/g, "\\$&")}]`, "g"), (ch) => "\\" + (ch || "s+")); //ch? "\\$&": "\\s+"); //+ tostr(more).replace(/[\s\S]/g, "\\$&").join("");
//    function esc1ch(ch) { return (ch == "\\")? "\\\\": ch? ("\\" + ch): "\\s+"); }
}


//make string safe for use in RHS of replace:
//ref: https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/String/replace#Specifying_a_string_as_a_parameter
function escrepl(str) { return tostr(str).replace(/\$/g, "$$$$"); } //CAUTION: double esc needed


//escape all newlines:
//makes debug or detecting multiple lines easier
//function escnl(str, want_color = true)
//{
//    return tostr(str).replace(NEWLINE_re, "\\n"[want_color? "cyan_lt": "nop"]); //draw attention to newlines (for easier debug)
//}


//esc all non-printable chars (except newline):
//optionally exclude ANSI color codes
function escnp(str, {want_color = true, keep_color = true, show_spaces = true, want_newline = false, radix = null, arysep = null} = {})
{
    const NONPRINT_xre = `
#        ( ${keep_color? "ANSI_COLOR().XRE()": "\\udead"} ) |  #CAUTION: need placeholder for non-color if using unnamed captures
        ${keep_color? `(?<keep> ${ANSI_COLOR()} ) |`: ""}  #CAUTION: need placeholder for non-color if using unnamed captures
        (?! \\n ) [^\\x20-\\x7e] |  #non-printable chars (except newline)
        [\\u0100-\\uffff]  #Unicode chars
#        [\\u0000-\\u001f\\u007f-\\uffff]  #non-printable or Unicode chars
        `/*.xre_tidy*/.XRE("gx");
//console.error(NONPRINT_xre.source);
//console.error(JSON.stringify(tostr(str)));
//console.error(JSON.stringify(tostr(str)));
    return tostr(str, radix, arysep)
//common special chars:
//        .replace(/\n/g, "\\n")
        .replace(/\r/g, "\\r")
        .replace(/\t/g, "\\t")
//        .replace(/\b/g, "\\b")
//        .replace(/\e/g, "\\e")
//all others:
//        .replace(/[\u0100-\uffff]/g, (uchar) => `\\u${("000" + uchar.charCodeAt(0).toString(16)).slice(-4)}`) //esc Unicode chars first so they aren't matched with other non-printables
//        .replace(/[\u0100-\uffff]/g, (uchar) => `\\u${uchar.charCodeAt(0).toString(16).padStart(4, "0")}`) //esc Unicode chars first so they aren't matched with other non-printables
//        .replace(/[^\x20-\x7e]/g, (match) => `\\x${hex(match.charCodeAt(0), false)}`);
        .replace(NONPRINT_xre, (chr/*, keep*/) => chr.keep || `\\u${chr.charCodeAt(0).toString(16).padStart(4, "0")}`.replace(/\\u00/g, "\\x")[want_color? "red_lt": "nop"]) //CAUTION: use named capture to avoid ofs/instr args
        [show_spaces? "replace": "nop"](/ /g, VisibleSpace) //make it easier to see white space
        [want_newline? "nop": "replace"](NEWLINE_re, "\\n"[want_color? "cyan_lt": "nop"]); //draw attention to newlines (for easier debug)
}


//remove esc chars:
//converts non-printable chars
function unesc(str)
{
    const ESCAPED_xre = `${ESC} ( ${ANYCHAR} )`.XRE();
    return tostr(str)
        .replace(/\\r/g, "\r")
        .replace(/\\t/g, "\t")
        .replace(/\\x/g, "\\u00")
        .replace(/\\u([0-9A-F]{4})/gi, (match, hex) => String.fromCharCode(parseInt(hex, 16)))
        .replace(ESCAPED_xre, "$1");
}


//remove blank lines:
//CAUTION: don't use on source fle (alters line#s)
function noblanks(str)
{
    return tostr(str).replace(/^\s*$(?:[\r\n]+)/gm, ""); //based on https://stackoverflow.com/questions/16369642/javascript-how-to-use-a-regular-expression-to-remove-blank-lines-from-a-string
}


//return ANSI color code pattern for regex:(chr.charCodeAt(0) < 0x100)? 2: 4
//pass color === true for any color (captured), falsey for end of color, undef for either
//NOTE: unnamed capture allows multiple usage within same regex
//NOTE: regex uses "x" (extended) format
function ANSI_COLOR(color) //, want_xre) //= true)
{
    const pattern = `\\x1B  #ASCII Escape char
        \\[
        ${(color === true)? "( [\\d;]+ )": //(?: \\d ; )? \\d+ )": //any color (captured)
          (color === false)? "0": //end of color
          color || //specific color
          "( [\\d;]+ | 0 )" //\\d ; \\d+ | 0 )" //any color start or end (captured)
          }
        m  #terminator
        `; //.xre_tidy;
    return pattern; //(want_xre /*!== false*/)? new XRegExp(pattern, "xg"): pattern; //(want_xre || "g")
}
//const HASCOLOR_xre = `${ANSI_COLOR(true)}`.XRE();


//strip colors from string:
function nocolors(str)
{
    return tostr(str).replace(ANSI_COLOR().XRE("gx"), ""); //ANYCOLOR_xre, "");
}


//add a color code to string:
//CAUTION: pass in color code, not name
//function addcolor(str, color_code)
//{
//    const Code2Name = "red_lt, green_lt, blue_lt, yellow_lt, cyan_lt, pink_lt, gray_dk".split(/\s*,\s*/).reduce((lkup, color_name) => { lkup[leftof("#"[color_name], "#")] = color_name; return lkup; }, {});
//    return color_code? tostr(str)[Code2Name[color_code]]: str;
//}

//get/apply latest color:
//helps with color-related OCD :P
function colorof(str, apply_to)
{
    const Code2Name = "red_lt, green_lt, blue_lt, yellow_lt, cyan_lt, pink_lt, gray_dk"
        .split(/\s*,\s*/)
        .reduce((lkup, color_name) => { lkup[leftof("#"[color_name], "#")] = color_name; return lkup; }, {});
    const colorof_xre = ANSI_COLOR(true).XRE(); //("gx"); //"g" to get last, !g to get first
    const parts = tostr(str).match(colorof_xre) || [];
    const latest = parts[0] && (Code2Name[parts[0]] || fatal(`unknown color: ${parts[0].escnp}`));
    return (arguments.length < 2)? latest: latest? tostr(apply_to)[latest]: apply_to;
}
//remove latest color reset:
//    function remove_endcolor(args)
//    {
//CAUTION: colors.js uses different codes for resets ("0" or "9"), so need regex rather than string compare
//        const ENDCOLOR = "%".red_lt.replace(/^.*%/, "");
//        const ENDCOLOR_re = /\x1b\[[0-9;]+m\s*$/;
//console.error(`red%: ${"%".red.length}:'${escall("%".red)}'`.yellow_lt);
//console.error(`red_lt%: ${"%".red_lt.length}:'${escall("%".red_lt)}'`.yellow_lt);
//console.error(`end color: ${ENDCOLOR.length}:'${escall(ENDCOLOR)}'`.yellow_lt);
//        const has_color = tostr(args[args.length - 1]).match(ENDCOLOR_re); //|| [""]; //slice(-ENDCOLOR.length) == ENDCOLOR)? ENDCOLOR: "";
//        if (has_color) args.push(args.pop().slice(0, has_color.index)); //-ENDCOLOR.length)); //move color after srcline
//        return (has_color || [""])[0];
//    }


//restore previous color at end of each color:
function color_fixup(thing)
{
//    const NOCOLOR = "".blue; //kludge: force color off
//    if (Array.isArray(thing)) return thing.map((item) => color_fixup(item)); //.push_fluent(NOCOLOR); //CAUTION: recursion
    const colors = [];
//    colors.save = function(arg) { return this.push_fluent(color_fixup.latest = arg); } //save latest color seen
//    colors.restore = function(arg) { return this.length? this.pop_fluent(): [color_fixup.latest || ""]; } //restore previous color seen
    const retval = tostr(thing).replace(COLOR_DETECT_xre, (match) => colors[match.start? "push_fluent": "pop_fluent"](match.start).top || match);
    return retval;
}


//OCD helper / satisfy Grammar Police:
function plural(thingy, multiple, single)
{
    const count = (typeof thingy == "object")? numkeys(thingy): thingy; //NOTE: arrays are objects
//    else if (count.length) count = count.length; //array
    plural.suffix = (count == 1)? single || "": multiple || "s";
    return thingy;
}
module.exports.plural = plural;


//compare strings, find offset of difference:
function strcmp(str1, str2, len)
{
    [str1, str2] = [tostr(str1), tostr(str2)];
    if (strcmp.IgnoreCase) [str1, str2, strcmp.IgnoreCase] = [str1.toUpperCase(), str2.toUpperCase(), false]; //auto-reset
    const cmplen = len || Math.min(str1.length, str2.length);
    for (strcmp.index = 0; strcmp.index < cmplen; ++strcmp.index) //scan fwd for first diff
    {
        const diff = str1.charCodeAt(strcmp.index) - str2.charCodeAt(strcmp.index);
        if (!diff) continue;
        for (strcmp.difflen = cmplen - strcmp.index; strcmp.difflen > 0; --strcmp.difflen) //scan bkwd for last diff
            if (str1[strcmp.index + strcmp.difflen - 1] != str2[strcmp.index + strcmp.difflen - 1]) break;
        return diff;
    }
    strcmp.difflen = Math.abs(str1.length - str2.length);
    return str1.length - str2.length;
}


//make it easier to see where error is:
function highlight(str, ofs, before, after)
{
//    const VisibleSpace = "\u00a4"; //String.fromCharCode(0xa4);
//    const color_re = /m(\d+)\x1b/; // /\d+/; //TODO: use ANSI_xre
//    if (!highlight.space) highlight.space = VisibleSpace; //String.fromCharCode(0xa4);
//++highlight.count || (highlight.count = 1);
//    let len_before, color_before = tostr(before).replace(color_re, (match, color) => { len_before = +color; return "m##\x1b"; });
//    if (!len_before) [len_before, color_before] = [before, "##"];
//    color_before = color_before.replace(/##/, str.slice(Math.max(ofs - len_before, 0), ofs).escnp).blue; //Math.max(ofs - 1, 0))).blue;
//    let len_after, color_after = tostr(after || before).replace(color_re, (match, color) => { len_after = +color; return "m##\x1b"; });
//    if (!len_after) [len_after, color_after] = [after || before, "##"];
//    color_after = color_after.replace(/##/, str.slice(ofs + 1, ofs + len_after).escnp).blue;
//if (highlight.count < 5) { console.error("before", before); console.error("color before", color_before); }
//debug(typeof str, typeof ofs, trunc(JSON.stringify(str), 80));
//debug(typeof str.slice(ofs, ofs + 1), trunc(JSON.stringify(str.slice(ofs, ofs + 1)), 80));
//debug(typeof str.slice(ofs, ofs + 1).escnp, trunc(JSON.stringify(str.slice(ofs, ofs + 1).escnp), 80));
//    return `${color_before}${str.slice(ofs, ofs + 1).escnp.replace(/ /, highlight.space || VisibleSpace).red}${color_after}`; //kludge: show something visible in place of space; //Math.max(ofs -1, 0)
    str = tostr(str); //.replace(/ /g, highlight.space || VisibleSpace); //kludge: show something visible in place of spaces; allows spaces to be colored; CAUTION: len shouldn't change
    const color_before = colorof(before) || "blue_lt", len_before = Math.abs(+nocolors(before || str.length || 5)); //optional negative
    const color_mid = colorof(ofs) || "red_lt", ofs_mid = +nocolors(ofs || 0);
    const color_after = colorof(after) || color_before, len_after = +nocolors(after || str.length || 5);
//    highlight.space = null; //auto-reset for next time
    return fmt(str.slice(Math.max(ofs_mid - len_before, 0), ofs_mid))[color_before] + fmt(str.charAt(ofs_mid))[color_mid] + fmt(str.slice(ofs_mid + 1, ofs_mid + len_after + 1))[color_after];

    function fmt(str) { return str; } //NO- let caller do this; escnp(str)/*.escnl*/; } //.replace(/ /g, VisibleSpace); }
}


//expr eval, trap errors:
//NOTE: no default retval; returns undef after error so caller can choose the appropriate value to use
//TODO: move to vm? (security doesn't matter here since it's just source code hacking anyway)
function eval_try(expr, param) //want_warnings = true)
{
    const want_warnings = isNaN(param) || +param, from_srcline = (param && isNaN(param))? param + ",": "";
//    var geval = eval; //call eval in global scope; https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/eval
    const geval = function my_eval(expr) { return Function(`"use strict"; return (${expr})`)(); }
    try { return eval_try.latest = debug(geval("(" + expr + ")"), "<:eval result".green_lt, "expr:".green_lt, expr, from_srcline + srcline(+1)); } //CAUTION: need aurrounding "()" to get return value
    catch (exc)
    {
//no: let caller init if needed        eval_try.latest = undefined;
        const func = (want_warnings /*!== false*/)? console.error: debug;
        func("eval EXC:".red_lt, exc, "expr:".red_lt, expr.escnp/*.escnl*/, from_srcline + srcline(+1));
    }
}
module.exports.eval_try = eval_try;


//replace undef value:
//safer than "||" in case value is falsey ("0", etc)
function isundef(thing, undef_value) //, def_value)
{
//    if (/*typeof undef_value == "undefined"*/ arguments.length < 2) return typeof thing == "undefined"; //just check if undefined
    return (typeof thing == "undefined")?
        (arguments.length < 2) || undef_value: //undefined: just check or return alternate value
//       (arguments.length < 3)? false: def_value; //|| thing; //defined: return value or alternate value
        (arguments.length > 1) && thing;
//    switch (arguments.length)
//    {
//        case 1: return typeof thing == "undefined"; //just check if undefined
//        case 2: return (typeof thing == "undefined")? undef_value: thing;
//        case 3: return (typeof thing == "undefined")? undef_value: def_value;
//    }
}
module.exports.isundef = isundef;


//NOTE: hard-coded date/time fmt
function date2str(when)
{
    if (!when) when = new Date(); //when ||= new Date(); //Date.now();
    return `${when.getMonth() + 1}/${when.getDate()}/${when.getFullYear()} ${when.getHours()}:${nn(when.getMinutes())}:${nn(when.getSeconds())}`;

    function nn(val) { return (val < 10)? "0" + val: val; }
}
module.exports.date2str = date2str;


//debug(unquoescape('"hello"'));
//debug(unquoescape('\\#not thing'));
//debug(unquoescape('-xa="b c"'));
//process.exit(0);
//function unquoescape(str)
//{
//    const UNESC_QUOTE_xre = XRegExp(`
//        (<! \\\\ ) ['"]  #unescaped quote; negative look-behind
//    |
//        [\\\\'"]  #esc and quote chars
//        `, "gx"); //"gmxy");
//    return tostr(str).replace(UNESC_QUOTE_xre, "");
//}


//add quotes around a string:
function quote(str, quotype)
{
    if (!quotype) quotype = ~tostr(str).indexOf('"')? "'": '"'; //try to choose quote type that doesn't occur within string
    return `${quotype}${tostr(str)}${quotype}`;
}
module.exports.quote = quote;


//strip quotes from a string:
//NOTE: returns null if not quoted
function unquote(str)
{
//    const QUOTE_xre = XRegExp(`
//        (?<quotype> ['"] )
//        (?<inner> .* )
//        \\k<quotype>  #string must begin and end with same quote type
//    `/*.spaceRE*/.anchorRE, "x");
//    XRegExp(`${quostr("inner")}`.anchorRE, "x");
    const QUOTE_xre = QUO_STR.anchorRE.XRE();
//    if (!str.match(QUOTE_xre)) throw `"${tostr(str)}" is not quoted`.red_lt;
//    return XRegExp.replace(tostr(str), QUOTE_xre, "$<inner>");
//    return tostr(str).replace(QUOTE_xre, "$<inner>");
//console.error(`unquote '${str || "NOSTR"}' = '${JSON.stringify(str.match(QUOTE_xre))}'`);
    return tostr(str).match(QUOTE_xre)? str.slice(1, -1): str;
}
module.exports.unquote = unquote;


//function pushline(str) { /*if (str)*/ this.push(`${escu(str)}\n`); } //maintain correct line#


//tagged template handler:
//function todo_XRE(str_parts, ...args)
//{
//    args.push(""); //add a matching empty value for last string template fragment
//    return str_parts.reduce((retval, part, inx) => retval + part + args[inx], "");
//debug(JSON.stringify(str_parts));
//debug(JSON.stringify(args));
//    return debug(str_parts.map((part, inx) => part + tostr(args[inx])).join("").xre_tidy, "<:xre");
//}


//show val as hex (with or without "0x" prefix):
//function hex(val, prefix) { return (((arguments.length < 2) || prefix)? "0x": "") + val.toString(16); }


//make large numbers easier to read:
function commas(num) { return num.toLocaleString(); } //grouping (1000s) default = true
module.exports.commas = commas;


//return #items in object or array:
function numkeys(obj) { return obj.hasOwnProperty("length")? obj.length: Object.keys(obj || {}).length; }
//function numkeys(thing) { return Object.keys(thing || {}).length; }
module.exports.numkeys = numkeys;


//return #lines in a string (fragment):
//function numlines(src, len) { return ((arguments.length > 1)? src.slice(0, len): tostr(src)).split(NEWLINE_re).length; }
function numlines(src, len) { return tostr(src)[(arguments.length > 1)? "slice": "nop"](0, len).split(NEWLINE_re).length; }


//placeholder function:
function nop(arg) { return arg; }


//convert to regex with global flag set:
//used for .replaceAll()
function togrex(thing)
{
    const retval = !XRegExp.isRegExp(thing)? new RegExp(escre(thing), "g"):
        ~(thing.flags || thing.xregexp.flags).indexOf("g")? thing: //"g" flag already set
        thing.xregexp? (thing.xregexp.raw_src || thing.xregexp.source).XRE("g" + thing.xregexp.flags): //use XRE() instead of new XRegExp() to set extra debug info
        new RegExp(thing.source, "g" + thing.flags);
//if (retval !== thing) debug("to global regex before:", JSON.stringify(thing), "after:", JSON.stringify({src: retval.source || retval.xregexp.source, flags: retval.flags || retval.xregexp.flags}));
    return retval;
}


//convert to string:
//use this if thing might be numeric; this is more correct than using || "" for falsey values
function tostr(thing, radix, arysep) //, prefix)
{
//    const RetVals = Object.defineProperties({},
//    {
//        number: { get() { return thing.toString(radix || 10); }, },
//        string: { get() { return thing; }, },
//        undefined: { get() { return ""; }, },
//    };
//    return RetVals[typeof thing] || "";
//    return (typeof thing == "number")? thing.toString(radix || 10):
//        ((typeof thing != "undefined") && (typeof thing != "string"))? thing.toString():
//        thing || "";
    return ((typeof thing == "number") || radix)? ((radix === "0x")? radix + thing.toString(16): (+thing).toString(radix || 10)):
        ((typeof thing == "string") || (typeof thing == "undefined"))? thing || "":
//        (thing === -16)? "0x" + thing.toString(16):
        Array.isArray(thing)? thing.join(arysep || ","):
        Buffer.isBuffer(thing)? thing.toString():
        XRegExp.isRegExp(thing)? thing.raw_src || thing.source || thing.xregexp.source:
        (typeof thing == "object")? json_tidy(CircularJSON.stringify(thing)):
        thing.toString(); //something other than Buffer or Object?
}


//create xregex:
function XRE(pattern, flags)
{
//    const [my_debug, ...args] = XRE.busy? [console.error, srcline(+2), srcline(+1), srcline()]: [debug, multi_srcline(+2, +1, +0)]; //CAUTION: avoid recursion
    const want_debug = XRE.debug;
    XRE.debug = false; //auto-reset; CAUTION: do this before other function calls to prevent recursion
//    if (XRE.busy) warn("XRE recursion");
//    if (!tostr(pattern).match(/\(\?<\w+/)) return new RegExp(); //no need for XRegExp
//        const COMMENTS_xre = `${NOT_QUOTED} ${NOT_ESC} \\# .* $`.XRE("gmx"); //delete regex comments
//    return unindent(str).replace(COMMENTS_xre, ""); ///*.replace(/\n\s*-/g, " ")*/.escnl; //remove comments and leading white space
    const retval = new XRegExp(pattern, flags || "x");
    if (retval.xregexp.source != pattern) Object.assign(retval, {raw_src: pattern, tidy_src: xre_tidy(pattern)}); //keep exact copy of source pattern (for cloning or debug); don't clutter if same
    retval.want_scope = ~(flags || "").indexOf("g")? 'all': 'one'; //kludge: force replace-all to work
    retval.srcline = [srcline(+2, true), srcline(+1, true)];
    retval.debug = want_debug;
    if (want_debug)
//    {
//        XRE.debug = false; //auto-reset; CAUTION: do this first to prevent recursion inside debug()
//        if (XRE.busy) warn(`XRE recursion ${srcline(+5)}${srcline(+3)}`); //CAUTION: debug() and multi_srcline() cause recursion
//        else
//        {
//debugger;
//            XRE.busy = true;
            (/*XRE.busy? console.error:*/ debug)("XRE:", json_tidy(JSON.stringify(retval, null, 2)), srcline(+2)); //CAUTION: don't use debug() inside XRE(); causes recursion
//            XRE.busy = false;
//        }
//    }
//    XRE.debug = false; //auto-reset
    return retval;
}


//show abreviated regex:
function xre_abbrev(xre, limit)
{
    const words = {};
    xre_tidy(xre).replace(/(?<!\\)[a-z]{2,}/gi, (word) => ++words[word]);
    const maxlen = Object.keys(words).reduce((result, word) => Math.max(result, word.length), 0);
//maxlen 3..5, keep words >= 2; maxlen 6..9, keep words >= 4
    return Object.keys(words).filter((word) => (word.length >= maxlen / 2))[limit? "slice": "nop"](0, limit).join("...");
}


//clean up XRE pattern for readability (easier debug):
//might also be required if newlines are stripped or interfere with comments
function xre_tidy(xre, max_spaces = 1)
{
//debugger;
    const COMMENTS_xre = `${NOT_QUOTED} ${NOT_ESC} (?<comment> \\# .* ) $`.XRE("gmx"); //delete regex comments
//    const CommentsNewlines_re = /(?<![\\])#.*\n|\n/g;  //strip comments + newlines in case caller comments out parent line
    return /*unindent*/tostr(xre)
        .replace(COMMENTS_xre, (match, comment) => comment? "": match) //remove comments and leading white space, preserve strings
        .replace(/\(\?\:\)/g, "") //kludge: hide what appears to be XregExp artifacts
        .replace(/\s+/g, " ".repeat(max_spaces)); //{2,} /*.replace(/\n\s*-/g, " ")*/.escnl; //condense white space (assumes "x" flag)
}


//make JSON a little easier to read (for debug):
function json_tidy(str) //...args)
{
//var test_val0 = JSON.doing_stringify;
//var test_val1 = ++JSON.doing_stringify;
//var test_val2 = ++JSON.doing_stringify? "yes": "no";
//console.error(typeof test_val0, test_val0, typeof test_val1, test_val1, typeof test_val2, test_val2);
//        if (++JSON.doing_stringify) return sv_json_stringify.apply(JSON, arguments); //JSON5 uses JSON; avoid infinite recursion
//        JSON.doing_stringify = 0;
//        return (tostr(JSON5.stringify.apply(JSON5, arguments)).replace(/,(?=\w)/gi, ", ").replace(/:/g, ": "); //put a space after ",:" for easier readability
//        const want_fixup = (arguments.length < 2) && "replace"; //leave as-is if caller is using custom fmter
//        if (JSON.busy) return JSON.saved_stringfy(...args);
//        JSON.busy = true;
    const retval = tostr(str) //JSON.stringify(...args))
//            .replace(/"(\w+)":/g, want_fixup? "$1: ": "$1:") //remove quotes from key names, put space after if no fmter passed in
//            /*.replace*/ [want_fixup || "nop_fluent"](/,(?=\w)/gi, ", "); //also put a space after "," for easier readability
            .replace(/,(?="?\w)/gi, ", ") //also put a space after "," for easier readability
            .replace(/"(?!\d)(\w+)":/g, "$1: ".blue_lt); //remove quotes from key names, put space after if no fmter passed in
//    return tostr(str).replace(/(\{)"|(,)"|"(:)/g, "$1$2$3"); //|#PEG-KLUDGE#\}/g, "$1$2$3"); //kludge: peg parser wants matched "}" here
//        JSON.busy = false;
        return retval;
//    }, JSON.stringify]; //CAUTION: ";" must be here else following line will be appended
}


//undo heredoc indents (easier debug, shouldn't affect functionality):
function unindent(str)
{
    const FIRST_INDENT_xre = `
        ^  #start of string or line ("m" flag)
        (?<indented>  ${WHITE_END} )  #white space but not newline
        `/*.xre_tidy*/.XRE("xgm");
    const parts = tostr(str).match(FIRST_INDENT_xre);
//debug(`first indent: ${typeof parts.indented} '${parts.indented || ""}'`)
    return parts? str.replace(`^${parts.indented}`.XRE("gm"), ""): str; //remove leading white space
}


//function json_tidy(str)
//{
//return str;
//    return tostr(str).replace(/(\{)"|(,)"|"(:)/g, "$1$2$3"); //|#PEG-KLUDGE#\}/g, "$1$2$3"); //kludge: peg parser wants matched "}" here
//}


//function dedupe(str)
//{
//    return tostr(str).split("").reduce((contents, char) => ~contents.indexOf(char)? contents: contents + char, "");
////    return Object.keys(tostr(str).split("").reduce((contents, char) => { ++contents[char]; return contents; }, {})).join("");
//}


function trunc(str, len) //, esc)
{
    var retval = tostr(str);
    if (retval.length > len) { retval = retval.slice(0, len)/*.rtrim()*/.replace(/\s+$/, ""); retval += ` ${commas(str.length - retval.length)} more...`.blue_lt; }
//    if (esc) retval = retval.escnp/*.escnl*/; //replace(/\r/g, "\\r").replace(/\n/g, "\\n");
    return retval;
}


function leftof(str, delim) //{ return tostr(str).replace(new RegExp(`^.*?${escre(delim)}`), ""); }
{
    const len = tostr(str).indexOf(delim);
    return /*(len != -1)*/~len? str.slice(0, len): str; //return whole string if not found
}


function rightof(str, delim) //{ return tostr(str).replace(new RegExp(`${escre(delim)}.*$`), ""); }
{
    const len = tostr(str).indexOf(delim);
    return /*(len != -1)*/~len? str.slice(len + delim.length): ""; //return empty if not found
}


//add anchors around RE pattern:
function anchorRE(str) { return `^(?:${tostr(str)})$`; } //CAUTION: need "()" in case str has embedded "|"


//remove anchors around RE pattern:
function unanchorRE(str)
{
//    return tostr(str).replace(/^\^(.*)\$$/, "$1");
    const UNANCH_xre = `
        \\^  \\(\\?:  (.*?)  \\)  \\$  #remove outer "(?: )" added by anchorRE()
      |
        \\^ (.*?) \\$
        `.anchorRE.XRE();
//console.error("unanchRE:", xre_tidy(UNANCH_xre.xregexp.source).escnl);
//console.error("unanch before:", str, srcline());
//console.error(" unanch after:", tostr(str).replace(UNANCH_xre, "$1$2"), srcline());
    return tostr(str).replace(UNANCH_xre, "$1$2");
}


//for (let m in this) console.error(typeof m, m);
debug("-".repeat(20).cyan_lt);
debug(`run at: ${date2str()}`.cyan_lt);
debug(`${__file} ${plural(numkeys(module.exports))} module export${plural.suffix}:`, Object.keys(module.exports).join(", "));
Object.assign(global, module.exports); //kludge: expose selected functions to eval() context

//eof