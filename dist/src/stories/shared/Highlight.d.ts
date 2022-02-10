import { ComponentProps, FunctionComponent } from 'react';
declare const HighlightBlock: import("styled-components").StyledComponent<"div", any, {}, never>;
declare const languageMap: {
    readonly mdx: "markdown";
    readonly bash: "bash";
    readonly javascript: "javascript";
    readonly typescript: "typescript";
    readonly json: "json";
    readonly css: "css";
    readonly yaml: "yaml";
    readonly markdown: "markdown";
    readonly md: "md";
    readonly jsx: "jsx";
    readonly tsx: "tsx";
};
interface Props {
    language?: keyof typeof languageMap;
    withHTMLChildren?: boolean;
}
export declare const Highlight: FunctionComponent<Props & ComponentProps<typeof HighlightBlock>>;
export {};
