import * as React from 'react';
export interface VdsPageTitleProps {
    /** Titolo da utilizzare come intestazione della pagina */
    title: string;
    /** Contenuto secondario ( VdsBreadcrumb o eventuale descrizione ) */
    content?: React.ReactElement | string;
    /** Eventuale callback pre gestire l'evento di torna indietro nel titolo della pagina */
    historyBackEvent?: () => void;
}
export declare const VdsPageTitle: React.VFC<VdsPageTitleProps>;
