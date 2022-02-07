import Alert from '@mui/material/Alert';
import { withStyles } from '@mui/styles';

const primary = {
    main: '#005075'
}
const success = {
    main: '#09822A'
}
const background = {
    default: '#FFFFFF'
}
const text = {
    primary: '#005075'
}
const warning = {
    main: '#FDB927'
}
const error = {
    main: '#D82829'
}

export const VdsAlert = withStyles(() => ({
  root: {
    backgroundColor: background.default,
    color: text.primary,
        borderRadius: 'unset',
        fontFamily: 'Roboto',
        fontWeight: '400',
        fontSize: '16px'
  },
  standardInfo: {
      border: `1px solid ${primary.main}`,
      color: primary.main,
      borderBottom: `3px solid ${primary.main}`,
      '& .MuiAlert-icon': {
          fill: primary.main
      },
    '& svg': {
          fill: primary.main
      }
  },
  standardSuccess: {
    border: `1px solid ${success.main}`,
      borderBottom: `3px solid ${success.main}`,
      color: success.main,
    '& .MuiAlert-icon': {
      fill: success
    }
  },
  standardWarning: {
    border: `1px solid ${warning.main}`,
      borderBottom: `3px solid ${warning.main}`,
      color: warning.main,
    '& .MuiAlert-icon': {
        fill: warning.main
    }
  },
  standardError: {
    border: `1px solid ${error.main}`,
      borderBottom: `3px solid ${error.main}`,
      color: error.main,
      '& .MuiAlert-icon': {
          fill: error.main
      },
      '& button': {
          fill: error.main
      }
  }
}))(Alert);
