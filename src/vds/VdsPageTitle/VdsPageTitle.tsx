import { IconButton, styled } from '@mui/material';
import * as React from 'react';
import { BiArrowBack } from 'react-icons/bi';

//#region Definizione dei tipi

export interface VdsPageTitleProps {
  /** Titolo da utilizzare come intestazione della pagina */
  title: string;
  /** Contenuto secondario ( VdsBreadcrumb o eventuale descrizione ) */
  content?: React.ReactElement | string;
  /** Eventuale callback pre gestire l'evento di torna indietro nel titolo della pagina */
  historyBackEvent?: () => void;
}

//#endregion

//#region StyledComponents

const StyledContainer = styled('div')({
  display: 'flex',
  alignItems: 'center',
  textAlign: 'center',
  borderBottom: '2px solid #0090D1',
  marginBottom: '24px',
  minHeight: 46,
  backgroundColor: 'white'
});

const StyledBackEventContainer = styled('div')({
  padding: '8px'
});

const StyledTitleContainer = styled('div')({
  fontSize: '16px',
  color: '#005075',
  lineHeight: "20px",
  letterSpacing: '0',
  fontFamily: 'Cairo SemiBold',
  fontWeight: 600,
  textAlign: 'center',
  textTransform: 'uppercase'
});

const StyledContentContainer = styled('div')({
  display: 'flex',
  justifyContent: 'center',
  fontSize: "12px",
  color: "#5A6872",
  letterSpacing: "0",
  fontFamily: "Roboto",
  fontWeight: 400,
  textAlign: "left"
});

const StyledPageTitleContainer = styled('div')({
  flexGrow: 1,
  display: 'flex',
  flexDirection: 'column'
});

const StyledIconButton = styled(IconButton)({
  borderRadius: 0
});
//#endregion

export const VdsPageTitle: React.VFC<VdsPageTitleProps> = (props) => {

  const { title, content, historyBackEvent } = props;

  return (
    <StyledContainer>
      {historyBackEvent && (
        <StyledBackEventContainer>
          <StyledIconButton onClick={historyBackEvent}>
            <BiArrowBack style={{ color: "#0090D1" }} />
          </StyledIconButton>
        </StyledBackEventContainer>
      )}
      <StyledPageTitleContainer>
        <StyledTitleContainer>
          {title}
        </StyledTitleContainer>
        {content && (
          <StyledContentContainer>
            {content}
          </StyledContentContainer>
        )}
      </StyledPageTitleContainer>
    </StyledContainer>
  );
};




















//const StyledTitleContainer = styled('div')(() => ({
//    'flex-grow': 1,
//    'display': 'flex',
//    'flexDirection': 'column',
//    padding: '8px 13px',
//    'justifyContent': 'center',
//    backgroundColor: 'white',
//    '& .title': {
//        'fontSize': '16px',
//        'color': '#005075',
//        'letterSpacing': '0',
//        'fontFamily': 'Cairo SemiBold',
//        'fontWeight': 600,
//        'textAlign': 'center'
//    },
//    '& .description': {
//        '& .MuiLink-root': {
//            fontWeight: 400,
//            'fontSize': '12px',
//            color: '#0090D1',
//            textDecoration: 'none!important'
//        },
//        '& :not(.MuiLink-root)': {
//            'fontSize': '12px',
//            color: '#005075',
//            fontStyle: 'bold',
//            fontWeight: 700
//        },
//        '& svg': {
//            'fontSize': '12px',
//            backgroundColor: 'white',
//            color: '#0090D1',
//        },
//        display: 'flex',
//        justifyContent: 'center',
//        'fontSize': '12px',
//        'color': '#5A6872',
//        'letterSpacing': '0',
//        'fontFamily': 'Roboto',
//        'lineHeight': "10px",
//        'fontWeight': 400,
//        'textAlign': 'center'
//    }
//}));

//export const VdsPageTitle: React.VFC<PageTitleProps> = (props: PageTitleProps) => {

//    const { title, content, historyBackEvent, textAlign = 'center' } = props;

//    return (
//        <StyledPageTitle>
//            <div style={{
//                display: 'flex',
//                alignItems: 'center',
//                textAlign: textAlign,
//                backgroundColor: 'white',
//                paddingLeft: '8px'
//            }}>
//                {historyBackEvent && <IconButton onClick={historyBackEvent}>
//                    <BiArrowBack
//                        style={{
//                            color: "#0090D1",
//                            fontWeight: 400
//                        }} />
//                </IconButton>}
//            </div>
//            <StyledTitleContainer>
//                <span className="title">{title.toUpperCase()}</span>
//                {content && <span className="description">{content}</span>}
//            </StyledTitleContainer>
//        </StyledPageTitle>
//    );
//}
